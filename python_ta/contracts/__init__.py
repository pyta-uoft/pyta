from typing import Any, Callable, List, Optional, Set
import sys
import typing
import inspect
import wrapt


def check_all_contracts(module_name: str = '__main__') -> None:
    """Automatically check contracts for all functions and classes in the given module.

    When called with no arguments, the current module's functions and classes are checked.
    """
    module = sys.modules[module_name]

    for name, value in inspect.getmembers(module):
        if inspect.isfunction(value):
            module.__dict__[name] = check_contracts(value)
        elif inspect.isclass(value):
            add_class_invariants(value)


@wrapt.decorator
def check_contracts(wrapped, instance, args, kwargs):
    """A decorator for automatically checking preconditions and type contracts for a function."""
    try:
        if instance and inspect.isclass(instance):
            # This is a class method, so there is no instance.
            return _check_function_contracts(wrapped, None, args, kwargs)
        else:
            return _check_function_contracts(wrapped, instance, args, kwargs)
    except AssertionError as e:
        raise AssertionError(str(e)) from None


def add_class_invariants(klass: type) -> None:
    """Modify the given class to check representation invariants and method contracts."""
    if '__representation_invariants__' in klass.__dict__:
        # This means the class has already been decorated
        return

    # Update representation invariants from this class' docstring and those of its superclasses.
    rep_invariants = set()

    # Iterate over all inherited classes except object
    for cls in klass.__mro__[:-1]:
        if '__representation_invariants__' in cls.__dict__:
            rep_invariants = rep_invariants.union(cls.__representation_invariants__)
        else:
            rep_invariants.update(parse_assertions(cls.__doc__ or '', parse_token='Representation Invariant'))

    setattr(klass, '__representation_invariants__', rep_invariants)

    def new_setattr(self: klass, name: str, value: Any) -> None:
        """Set the value of the given attribute on self to the given value.

        Check representation invariants for this class when not within an instance method of the class.
        """
        super(klass, self).__setattr__(name, value)
        curframe = inspect.currentframe()
        callframe = inspect.getouterframes(curframe, 2)
        frame_locals = callframe[1].frame.f_locals
        if self is not frame_locals.get('self'):
            # Only validating if the attribute is not being set in a instance/class method
            init = getattr(klass, '__init__')
            try:
                _check_invariants(self, rep_invariants, init.__globals__)
            except AssertionError as e:
                raise AssertionError(str(e)) from None

    for attr, value in klass.__dict__.items():
        if inspect.isroutine(value):
            if isinstance(value, (staticmethod, classmethod)):
                # Don't check rep invariants for staticmethod and classmethod
                setattr(klass, attr, check_contracts(value))
            else:
                setattr(klass, attr, _instance_method_wrapper(value, rep_invariants))

    klass.__setattr__ = new_setattr


def _check_function_contracts(wrapped, instance, args, kwargs):
    params = wrapped.__code__.co_varnames[:wrapped.__code__.co_argcount]
    annotations = typing.get_type_hints(wrapped)
    args_with_self = (instance,) + args if instance else args

    # Check function parameter types
    for arg, param in zip(args_with_self, params):
        if param in annotations:
            assert check_type_annotation(annotations[param], arg),\
                f'{wrapped.__name__} argument {repr(arg)} did not match type annotation for parameter "{param}: {annotations[param]}"'

    # Check function preconditions
    preconditions = parse_assertions(wrapped.__doc__ or '')
    function_locals = dict(zip(params, args_with_self))
    _check_assertions(wrapped, function_locals, preconditions)

    # Check return type
    r = wrapped(*args, **kwargs)
    if 'return' in annotations:
        return_type = annotations['return']
        assert check_type_annotation(return_type, r),\
            f'{wrapped.__name__} return value {r} does not match annotated return type {return_type.__name__}'

    return r


def _instance_method_wrapper(wrapped, rep_invariants=None):
    if rep_invariants is None:
        return check_contracts

    @wrapt.decorator
    def wrapper(wrapped, instance, args, kwargs):
        init = getattr(instance, '__init__')
        try:
            r = _check_function_contracts(wrapped, instance, args, kwargs)
            _check_invariants(instance, rep_invariants, init.__globals__)
        except AssertionError as e:
            raise AssertionError(str(e)) from None
        else:
            return r

    return wrapper(wrapped)


def _check_invariants(instance, rep_invariants: Set[str], global_scope: dict) -> None:
    """Check that the representation invariants for the instance are satisfied.
    """
    for invariant in rep_invariants:
        try:
            check = eval(invariant, global_scope, {'self': instance})
        except:
            print(f'[python_ta] Warning: could not evaluate invariant: {invariant}', file=sys.stderr)
        else:
            assert check,\
                f'Representation invariant "{invariant}" violated.'


def _check_assertions(wrapped: Callable[..., Any], function_locals: dict, assertions: List[str]) -> None:
    """Check that the given assertions are still satisfied.
    """
    for assertion in assertions:
        try:
            check = eval(assertion, wrapped.__globals__, function_locals)
        except:
            print(f'[python_ta] Warning: could not evaluate invariant: {assertion}', file=sys.stderr)
        else:
            assert check,\
                f'{wrapped.__name__} precondition "{assertion}" violated for arguments {function_locals}.'


def check_type_annotation(annotation: Optional[type], v: Any) -> bool:
    """Return whether v is compatible with the given type annotation.
    """
    if annotation is None:
        return v is None

    # TODO: Use typing.get_origin and typing.get_args in Python 3.8
    origin = getattr(annotation, '__origin__', None)

    if origin is None:
        return isinstance(v, annotation)
    else:
        origin_args = annotation.__args__
        if not isinstance(v, origin):
            return False
        elif origin is list:
            return all(check_type_annotation(origin_args[0], x) for x in v)
        else:
            return True


def parse_assertions(docstring: str, parse_token: str = 'Precondition') -> List[str]:
    """Return a list of preconditions/representation invariants parsed from the given docstring.
    Uses parse_token to determine what to look for. parse_token defaults to Precondition.

    Currently only supports two forms:

    1. A single line of the form "<parse_token>: <cond>"
    2. A group of lines starting with "<parse_token>s:", where each subsequent
       line is of the form "- <cond>". Each line is considered a separate condition.
       The lines can be separated by blank lines, but no other text.
    """
    lines = [line.strip() for line in docstring.split('\n')]
    assertion_lines = [i
                       for i, line in enumerate(lines)
                       if line.lower().startswith(parse_token.lower())]

    if assertion_lines == []:
        return []

    first = assertion_lines[0]
    if lines[first].startswith(parse_token + ':'):
        return [lines[first][len(parse_token + ':'):].strip()]
    elif lines[first].startswith(parse_token + 's:'):
        assertions = []
        for line in lines[first + 1:]:
            if line.startswith('-'):
                assertions.append(line[1:].strip())
            elif line != '':
                break
        return assertions
    else:
        return []
