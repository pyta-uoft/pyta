import inspect
import sys
import typing
from typing import Any, Callable, List, Optional, Set

import wrapt
from typeguard import check_type

DEBUG_CONTRACTS = False
"""
Set to True to display debugging messages when checking contracts.
"""

_DEFAULT_MAX_VALUE_LENGTH = 30
FUNCTION_RETURN_VALUE = "$return_value"


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
    if "__representation_invariants__" in klass.__dict__:
        # This means the class has already been decorated
        return

    # Update representation invariants from this class' docstring and those of its superclasses.
    rep_invariants = set()

    # Iterate over all inherited classes except builtins
    for cls in reversed(klass.__mro__):
        if "__representation_invariants__" in cls.__dict__:
            rep_invariants = rep_invariants.union(cls.__representation_invariants__)
        elif cls.__module__ != "builtins":
            rep_invariants.update(parse_assertions(cls, parse_token="Representation Invariant"))

    setattr(klass, "__representation_invariants__", rep_invariants)

    def new_setattr(self: klass, name: str, value: Any) -> None:
        """Set the value of the given attribute on self to the given value.

        Check representation invariants for this class when not within an instance method of the class.
        """
        cls_annotations = typing.get_type_hints(klass)

        if name in cls_annotations:
            try:
                _debug(f"Checking type of attribute {attr} for {klass.__qualname__} instance")
                check_type(name, value, cls_annotations[name])
            except TypeError:
                raise AssertionError(
                    f"Value {_display_value(value)} did not match type annotation for attribute "
                    f"{name}: {_display_annotation(cls_annotations[name])}"
                ) from None

        super(klass, self).__setattr__(name, value)
        curframe = inspect.currentframe()
        callframe = inspect.getouterframes(curframe, 2)
        frame_locals = callframe[1].frame.f_locals
        if self is not frame_locals.get("self"):
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
    params = wrapped.__code__.co_varnames[: wrapped.__code__.co_argcount]
    annotations = typing.get_type_hints(wrapped)
    args_with_self = args if instance is None else (instance,) + args

    # Check function parameter types
    for arg, param in zip(args_with_self, params):
        if param in annotations:
            try:
                _debug(f"Checking type of parameter {param} in call to {wrapped.__qualname__}")
                check_type(param, arg, annotations[param])
            except TypeError:
                additional_suggestions = _get_argument_suggestions(arg, annotations[param])

                raise PyTAContractError(
                    f"{wrapped.__name__} argument {_display_value(arg)} did not match type "
                    f"annotation for parameter {param}: {_display_annotation(annotations[param])}"
                    + (f"\n{additional_suggestions}" if additional_suggestions else "")
                )

    # Check function preconditions
    preconditions = parse_assertions(wrapped)
    function_locals = dict(zip(params, args_with_self))
    _check_assertions(wrapped, function_locals, preconditions)

    # Check return type
    r = wrapped(*args, **kwargs)
    if "return" in annotations:
        return_type = annotations["return"]
        try:
            _debug(f"Checking return type from call to {wrapped.__qualname__}")
            check_type("return", r, return_type)
        except TypeError:
            raise PyTAContractError(
                f"{wrapped.__name__}'s return value {_display_value(r)} did not match "
                f"return type annotation {_display_annotation(return_type)}"
            )

    # Check function postconditions
    postconditions = parse_assertions(wrapped, parse_token="Postcondition")
    _check_assertions(
        wrapped,
        function_locals,
        postconditions,
        condition_type="postcondition",
        function_return_val=r,
    )

    return r


def _get_argument_suggestions(arg: Any, annotation: type) -> str:
    """Returns potential suggestions for the given arg and its annotation"""
    try:
        if isinstance(arg, type) and issubclass(arg, annotation):
            return "Did you mean {cls}(...) instead of {cls}?".format(cls=arg.__name__)
    except TypeError:
        pass

    return ""


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
        frame_context_self = frame.f_locals.get("self")
        frame_context_vars = frame.f_code.co_varnames
        if (
            frame_context_name == "__init__"
            and frame_context_self is instance
            and frame_context_vars[0] == "self"
        ):
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
            _debug(f"Checking type of attribute {attr} for {klass.__qualname__} instance")
            check_type(attr, value, annotation)
        except TypeError:
            raise AssertionError(
                f"{_display_value(value)} did not match type annotation for attribute {attr}: "
                f"{_display_annotation(annotation)}"
            )


def _check_invariants(instance, klass: type, global_scope: dict) -> None:
    """Check that the representation invariants for the instance are satisfied."""
    rep_invariants = getattr(klass, "__representation_invariants__", set())

    for invariant in rep_invariants:
        try:
            _debug(
                "Checking representation invariant for "
                f"{instance.__class__.__qualname__}: {invariant}"
            )
            check = eval(invariant, {**global_scope, "self": instance})
        except:
            _debug(f"Warning: could not evaluate representation invariant: {invariant}")
        else:
            if not check:
                raise PyTAContractError(f'Representation invariant "{invariant}" was violated')


def _get_legal_return_val_var_name(var_dict: dict) -> str:
    """
    Add '_' to the end of __function_return_value__ until a variable name that has not been used for any other
    variable in the function's scope is created. This is used to refer to the function's return value when evaluating
    postconditions.
    """
    legal_var_name = "__function_return_value__"

    while legal_var_name in var_dict:
        legal_var_name += "_"

    return legal_var_name


def _replace_return_val_assertion(assertion: str, return_val_var_name: Optional[str]) -> str:
    """
    Replace FUNCTION_RETURN_VALUE in the assertion with the legal python variable name generated and return the new
    assertion. If FUNCTION_RETURN_VALUE does not appear in assertion, then simply return the original assertion.

    Precondition: If FUNCTION_RETURN_VALUE is in assertion, then return_val_var_name is not None
    """

    if FUNCTION_RETURN_VALUE in assertion:
        return assertion.replace(FUNCTION_RETURN_VALUE, return_val_var_name)
    return assertion


def _check_assertions(
    wrapped: Callable[..., Any],
    function_locals: dict,
    assertions: List[str],
    condition_type: str = "precondition",
    function_return_val: Any = None,
) -> None:
    """Check that the given assertions are still satisfied."""
    return_val_dict, return_val_var_name = {}, None

    if condition_type == "postcondition":
        return_val_var_name = _get_legal_return_val_var_name(
            {**wrapped.__globals__, **function_locals}
        )
        return_val_dict[return_val_var_name] = function_return_val

    for assertion in assertions:
        try:
            _debug(f"Checking {condition_type} for {wrapped.__qualname__}: {assertion}")
            replaced_assertion = _replace_return_val_assertion(assertion, return_val_var_name)
            check = eval(
                replaced_assertion, {**wrapped.__globals__, **function_locals, **return_val_dict}
            )
        except:
            _debug(f"Warning: could not evaluate {condition_type}: {assertion}")
        else:
            if not check:
                arg_string = ", ".join(
                    f"{k}: {_display_value(v)}" for k, v in function_locals.items()
                )
                arg_string = "{" + arg_string + "}"

                return_val_string = ""

                if condition_type == "postcondition":
                    return_val_string = f"and return value {function_return_val}"

                raise PyTAContractError(
                    f'{wrapped.__name__} {condition_type} "{assertion}" was '
                    f"violated for arguments {arg_string} {return_val_string}"
                )


def parse_assertions(obj: Any, parse_token: str = "Precondition") -> List[str]:
    """Return a list of preconditions/postconditions/representation invariants parsed from the given entity's docstring.

    Uses parse_token to determine what to look for. parse_token defaults to Precondition.

    Currently only supports two forms:

    1. A single line of the form "<parse_token>: <cond>"
    2. A group of lines starting with "<parse_token>s:", where each subsequent
       line is of the form "- <cond>". Each line is considered a separate condition.
       The lines can be separated by blank lines, but no other text.
    """
    docstring = getattr(obj, "__doc__") or ""
    lines = [line.strip() for line in docstring.split("\n")]
    assertion_lines = [
        i for i, line in enumerate(lines) if line.lower().startswith(parse_token.lower())
    ]

    if assertion_lines == []:
        return []

    first = assertion_lines[0]

    if lines[first].startswith(parse_token + ":"):
        return [lines[first][len(parse_token + ":") :].strip()]
    elif lines[first].startswith(parse_token + "s:"):
        assertions = []
        for line in lines[first + 1 :]:
            if line.startswith("-"):
                assertion = line[1:].strip()
                _debug(f"Adding assertion to {obj.__qualname__}: {assertion}")
                assertions.append(assertion)
            elif line != "":
                break
        return assertions
    else:
        return []


def _display_value(value: Any, max_length: int = _DEFAULT_MAX_VALUE_LENGTH) -> str:
    """Return a human-friendly representation of the given value.

    If DEBUG_CONTRACTS is False, truncate long strings to max_length characters.

    Preconditions:
        - max_length >= 5
    """
    s = repr(value)
    if not DEBUG_CONTRACTS and len(s) > max_length:
        i = (max_length - 3) // 2
        return s[:i] + "..." + s[-i:]
    else:
        return s


def _display_annotation(annotation: Any) -> str:
    """Return a human-friendly representation of the given type annotation.

    >>> _display_annotation(int)
    'int'
    >>> _display_annotation(list[int])
    'list[int]'
    >>> from typing import List
    >>> _display_annotation(List[int])
    'typing.List[int]'
    """
    if annotation is type(None):  # Use 'None' instead of 'NoneType'
        return "None"
    if hasattr(annotation, "__origin__"):  # Generic type annotations
        return repr(annotation)
    elif hasattr(annotation, "__name__"):
        return annotation.__name__
    else:
        return repr(annotation)


def _debug(msg: str) -> None:
    """Display a debugging message.

    Do nothing if DEBUG_CONTRACTS is False.
    """
    if not DEBUG_CONTRACTS:
        return

    print("[PyTA]", msg, file=sys.stderr)
