from typing import Any, Callable, List, Optional, Set
from typeguard import check_type
import sys
import typing
import inspect
import wrapt


DEBUG_CONTRACTS = False
"""
Set to True to display debugging messages when checking contracts.
"""


class PyTAContractError(Exception):
    """Error raised when a PyTA contract assertion is violated."""


def check_all_contracts(*mod_names: str, decorate_main: bool = True) -> None:
    """Automatically check contracts for all functions and classes in the given modules.

    By default (when called with no arguments), the current module is used.

    Args:
        *mod_names: The names of modules to check contracts for. These modules must have been
            previously imported.
        decorate_main: True if the module being run (where __name__ == '__main__') should
            have contracts checked.
    """

    modules = []
    if decorate_main:
        modules.append(sys.modules["__main__"])

    for module_name in mod_names:
        modules.append(sys.modules.get(module_name, None))

    for module in modules:
        if not module:
            # Module name was passed in incorrectly.
            continue
        for name, value in inspect.getmembers(module):
            if inspect.isfunction(value) or inspect.isclass(value):
                module.__dict__[name] = check_contracts(value)


@wrapt.decorator
def _enable_function_contracts(wrapped, instance, args, kwargs):
    """A decorator that enables checking contracts for a function."""
    try:
        if instance and inspect.isclass(instance):
            # This is a class method, so there is no instance.
            return _check_function_contracts(wrapped, None, args, kwargs)
        else:
            return _check_function_contracts(wrapped, instance, args, kwargs)
    except PyTAContractError as e:
        raise AssertionError(str(e)) from None


def check_contracts(func_or_class: Any) -> Callable:
    """A decorator to enable contract checking for a function or class.

    When used with a class, all methods defined within the class have contract checking enabled.

    Example:

        >>> from python_ta.contracts import check_contracts
        >>> @check_contracts
        ... def divide(x: int, y: int) -> int:
        ...     \"\"\"Return x // y.
        ...
        ...     Preconditions:
        ...        - y != 0
        ...     \"\"\"
        ...     return x // y
    """
    if inspect.isroutine(func_or_class):
        return _enable_function_contracts(func_or_class)
    elif inspect.isclass(func_or_class):
        add_class_invariants(func_or_class)
        return func_or_class
    else:
        # Default action
        return func_or_class


def add_class_invariants(klass: type) -> None:
    """Modify the given class to check representation invariants and method contracts."""
    if '__representation_invariants__' in klass.__dict__:
        # This means the class has already been decorated
        return

    # Update representation invariants from this class' docstring and those of its superclasses.
    rep_invariants = set()

    # Iterate over all inherited classes except builtins
    for cls in reversed(klass.__mro__):
        if '__representation_invariants__' in cls.__dict__:
            rep_invariants = rep_invariants.union(cls.__representation_invariants__)
        elif cls.__module__ != 'builtins':
            rep_invariants.update(parse_assertions(cls, parse_token='Representation Invariant'))

    setattr(klass, '__representation_invariants__', rep_invariants)

    def new_setattr(self: klass, name: str, value: Any) -> None:
        """Set the value of the given attribute on self to the given value.

        Check representation invariants for this class when not within an instance method of the class.
        """
        cls_annotations = typing.get_type_hints(klass)

        if name in cls_annotations:
            try:
                _debug(f'Checking type of attribute {attr} for {klass.__qualname__} instance')
                check_type(name, value, cls_annotations[name])
            except TypeError:
                raise AssertionError(
                    f'{repr(value)} did not match type annotation for attribute "{name}: {cls_annotations[name]}"') from None

        super(klass, self).__setattr__(name, value)
        curframe = inspect.currentframe()
        callframe = inspect.getouterframes(curframe, 2)
        frame_locals = callframe[1].frame.f_locals
        if self is not frame_locals.get('self'):
            # Only validating if the attribute is not being set in a instance/class method
            klass_mod = sys.modules.get(klass.__module__)
            if klass_mod is not None:
                try:
                    _check_invariants(self, klass, klass_mod.__dict__)
                except PyTAContractError as e:
                    raise AssertionError(str(e)) from None

    for attr, value in klass.__dict__.items():
        if inspect.isroutine(value):
            if isinstance(value, (staticmethod, classmethod)):
                # Don't check rep invariants for staticmethod and classmethod
                setattr(klass, attr, check_contracts(value))
            else:
                setattr(klass, attr, _instance_method_wrapper(value, klass))

    klass.__setattr__ = new_setattr


def _check_function_contracts(wrapped, instance, args, kwargs):
    params = wrapped.__code__.co_varnames[:wrapped.__code__.co_argcount]
    annotations = typing.get_type_hints(wrapped)
    args_with_self = args if instance is None else (instance,) + args

    # Check function parameter types
    for arg, param in zip(args_with_self, params):
        if param in annotations:
            try:
                _debug(f'Checking type of parameter {param} in call to {wrapped.__qualname__}')
                check_type(param, arg, annotations[param])
            except TypeError:
                raise PyTAContractError(
                    f'{wrapped.__name__} argument {repr(arg)} did not match type annotation for parameter '
                    f'"{param}: {annotations[param]}"')

    # Check function preconditions
    preconditions = parse_assertions(wrapped)
    function_locals = dict(zip(params, args_with_self))
    _check_assertions(wrapped, function_locals, preconditions)

    # Check return type
    r = wrapped(*args, **kwargs)
    if 'return' in annotations:
        return_type = annotations['return']
        try:
            _debug(f'Checking return type from call to {wrapped.__qualname__}')
            check_type('return', r, return_type)
        except TypeError:
            raise PyTAContractError(
                f'{wrapped.__name__} return value {r} does not match annotated return type {return_type}')

    return r


def _instance_method_wrapper(wrapped: Callable, klass: type) -> Callable:

    @wrapt.decorator
    def wrapper(wrapped, instance, args, kwargs):
        try:
            r = _check_function_contracts(wrapped, instance, args, kwargs)
            if _instance_init_in_callstack(instance):
                return r
            _check_class_type_annotations(klass, instance)
            klass_mod = sys.modules.get(klass.__module__)
            if klass_mod is not None:
                _check_invariants(instance, klass, klass_mod.__dict__)
        except PyTAContractError as e:
            raise AssertionError(str(e)) from None
        else:
            return r

    return wrapper(wrapped)


def _instance_init_in_callstack(instance: Any) -> bool:
    """Return whether instance's init is part of the current callstack

    Note: due to the nature of the check, externally defined __init__ functions with
    'self' defined as the first parameter may pass this check.
    """
    frame = inspect.currentframe().f_back
    while frame:
        frame_context_name = inspect.getframeinfo(frame).function
        frame_context_self = frame.f_locals.get('self')
        frame_context_vars = frame.f_code.co_varnames
        if (frame_context_name == '__init__' and frame_context_self is instance
                and frame_context_vars[0] == 'self'):
            return True
        frame = frame.f_back
    return False


def _check_class_type_annotations(klass: type, instance: Any) -> None:
    """Check that the type annotations for the class still hold.

    Precondition:
        - isinstance(instance, klass)
    """
    cls_annotations = typing.get_type_hints(klass)

    for attr, annotation in cls_annotations.items():
        value = getattr(instance, attr)
        try:
            _debug(f'Checking type of attribute {attr} for {klass.__qualname__} instance')
            check_type(attr, value, annotation)
        except TypeError:
            raise AssertionError(
                f'{repr(value)} did not match type annotation for attribute "{attr}: {annotation}"')


def _check_invariants(instance, klass: type, global_scope: dict) -> None:
    """Check that the representation invariants for the instance are satisfied.

    """
    rep_invariants = getattr(klass, '__representation_invariants__', set())

    for invariant in rep_invariants:
        try:
            _debug(f'Checking representation invariant for {instance.__class__.__qualname__}: {invariant}')
            check = eval(invariant, {**global_scope, 'self': instance})
        except:
            _debug(f'Warning: could not evaluate representation invariant: {invariant}')
        else:
            if not check:
                raise PyTAContractError(f'Representation invariant "{invariant}" violated.')


def _check_assertions(wrapped: Callable[..., Any], function_locals: dict, assertions: List[str]) -> None:
    """Check that the given assertions are still satisfied.
    """
    for assertion in assertions:
        try:
            _debug(f'Checking precondition for {wrapped.__qualname__}: {assertion}')
            check = eval(assertion, {**wrapped.__globals__, **function_locals})
        except:
            _debug(f'Warning: could not evaluate precondition: {assertion}')
        else:
            if not check:
                raise PyTAContractError(f'{wrapped.__name__} precondition "{assertion}" '
                                        f'violated for arguments {function_locals}.')


def parse_assertions(obj: Any, parse_token: str = 'Precondition') -> List[str]:
    """Return a list of preconditions/representation invariants parsed from the given entity's docstring.

    Uses parse_token to determine what to look for. parse_token defaults to Precondition.

    Currently only supports two forms:

    1. A single line of the form "<parse_token>: <cond>"
    2. A group of lines starting with "<parse_token>s:", where each subsequent
       line is of the form "- <cond>". Each line is considered a separate condition.
       The lines can be separated by blank lines, but no other text.
    """
    docstring = getattr(obj, '__doc__') or ''
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
                assertion = line[1:].strip()
                _debug(f'Adding assertion to {obj.__qualname__}: {assertion}')
                assertions.append(assertion)
            elif line != '':
                break
        return assertions
    else:
        return []


def _debug(msg: str) -> None:
    """Display a debugging message.

    Do nothing if DEBUG_CONTRACTS is False.
    """
    if not DEBUG_CONTRACTS:
        return

    print('[PyTA]', msg, file=sys.stderr)
