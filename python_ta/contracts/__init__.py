from typing import Any, List, Optional
import typing
import inspect
import wrapt


class InvalidAssertion(Exception):
    """Exception raised when a Assertion is invalid
    """


@wrapt.decorator
def check_contracts(wrapped, instance, args, kwargs):
    if instance is None and inspect.isclass(wrapped):
        return add_class_contracts(wrapped, args, kwargs)
    else:
        return check_function_contracts(wrapped, instance, args, kwargs)


def add_class_contracts(wrapped, args, kwargs):
    rep_invariants = parse_assertions(
        wrapped.__doc__ or '', parse_token="Representation Invariant")
    setattr(wrapped, "__representation_invariants__", rep_invariants)

    def new_setattr(self, name, value):
        super_class = wrapped.__mro__[1]
        super_class.__setattr__(self, name, value)
        curframe = inspect.currentframe()
        callframe = inspect.getouterframes(curframe, 2)
        frame_members = dict((name, member) for name,
                             member in inspect.getmembers(callframe[1].frame))
        frame_locals = frame_members['f_locals']
        if self is not frame_locals.get('self'):
            # Only validating if the attribute is not being set in a instance/class method
            init = getattr(wrapped, "__init__")
            check_invariants(self, init.__globals__)

    for attr in wrapped.__dict__:
        if callable(getattr(wrapped, attr)):
            setattr(wrapped, attr, check_contracts(getattr(wrapped, attr)))

    wrapped.__setattr__ = new_setattr

    return wrapped(*args, **kwargs)


def check_function_contracts(wrapped, instance, args, kwargs):
    params = wrapped.__code__.co_varnames[:wrapped.__code__.co_argcount]
    annotations = typing.get_type_hints(wrapped)

    args_with_self = (instance,) + args if instance else args

    for arg, param in zip(args_with_self, params):
        if param in annotations:
            assert check_type_annotation(annotations[param], arg),\
                f'Argument {repr(arg)} did not match type annotation for parameter "{param}: {annotations[param]}"'

    preconditions = parse_assertions(wrapped.__doc__ or '')

    function_locals = dict(zip(params, args_with_self))
    check_assertions(wrapped, function_locals, preconditions)

    r = wrapped(*args, **kwargs)

    if instance and hasattr(type(instance), "__representation_invariants__"):
        init = getattr(instance, "__init__")
        check_invariants(instance, init.__globals__)

    if 'return' in annotations:
        return_type = annotations['return']
        assert check_type_annotation(return_type, r),\
            f'Return value {r} does not match annotated return type {return_type.__name__}'
    return r


def check_invariants(instance, global_scope):
    """
    Checks to see if the representation invariants for the instance are satisfied.
    """
    for invariant in type(instance).__representation_invariants__:
        try:
            check = eval(invariant, global_scope, {"self": instance})
        except:
            # TODO: Decide what to do here, e.g. "Invalid invariant"
            raise InvalidAssertion(
                f'Error evaluating invariant: {invariant}')
        else:
            assert check,\
                f'Invariant "{invariant}" violated.'


def check_assertions(wrapped, function_locals, assertions):
    """
    Checks if the assertions are still satisfied.
    """
    for assertion in assertions:
        try:
            check = eval(assertion, wrapped.__globals__, function_locals)
        except:
            # TODO: Decide what to do here, e.g. "Invalid assertion"
            raise InvalidAssertion(
                f'Error evaluating assertion: {assertion}')
        else:
            assert check,\
                f'Assertion "{assertion}" violated for arguments {function_locals}'


def check_type_annotation(annotation: Optional[type], v: Any) -> bool:
    """
    Return whether v is compatible with the given type annotation.
    """
    if annotation is None:
        return v is None

    # TODO: Use typing.get_origin and typing.get_args in Python 3.8
    origin = getattr(annotation, '__origin__', None)\

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


def parse_assertions(docstring: str, parse_token: str = "Precondition") -> List[str]:
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
