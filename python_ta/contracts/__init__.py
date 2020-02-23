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
    return check_function_contracts(wrapped, instance, args, kwargs)


def add_class_contracts(wrapped, args, kwargs):
    rep_invariants = parse_conditions(
        wrapped.__doc__ or '', parse_token="Representation Invariant")
    setattr(wrapped, "__representation_invariants__", rep_invariants)

    def new_setattr(self, name, value):
        super_class = wrapped.__mro__[1]
        super_class.__setattr__(self, name, value)
        curframe = inspect.currentframe()
        callframe = inspect.getouterframes(curframe, 2)
        if callframe[1][3] not in wrapped.__dict__:
            # Only validating if the attribute is not being set in a instance/class method
            validate_invariants(wrapped, self)

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

    preconditions = parse_conditions(wrapped.__doc__ or '')

    function_locals = dict(zip(params, args_with_self))
    validate_conditions(wrapped, function_locals, preconditions)

    r = wrapped(*args, **kwargs)

    if instance and hasattr(type(instance), "__representation_invariants__"):
        validate_conditions(wrapped, function_locals,
                            type(instance).__representation_invariants__)

    if 'return' in annotations:
        return_type = annotations['return']
        assert check_type_annotation(return_type, r),\
            f'Return value {r} does not match annotated return type {return_type.__name__}'
    return r


def validate_invariants(cls, instance):
    for invariant in type(instance).__representation_invariants__:
        try:
            check = eval(invariant, {"self": instance})
        except:
            # TODO: Decide what to do here, e.g. "Invalid invariant"
            raise InvalidAssertion(
                f'Error evaluating invariant: {invariant}')
        else:
            assert check,\
                f'Invariant "{invariant}" violated.'


def validate_conditions(wrapped, function_locals, assertions):
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
    """Return whether v is compatible with the given type annotation."""
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


def parse_conditions(docstring: str, parse_token: str = "Precondition") -> List[str]:
    """Return a list of preconditions/representation invariants parsed from the given docstring. 
    Uses parse_token to determine what to look for. parse_token defaults to Precondition.

    Currently only supports two forms:

    1. A single line of the form "<parse_token>: <cond>"
    2. A group of lines starting with "<parse_token>s:", where each subsequent
       line is of the form "- <cond>". Each line is considered a separate condition.
       The lines can be separated by blank lines, but no other text.
    """
    lines = [line.strip() for line in docstring.split('\n')]
    condition_lines = [i
                       for i, line in enumerate(lines)
                       if line.lower().startswith(parse_token.lower())]

    if condition_lines == []:
        return []

    first = condition_lines[0]
    if lines[first].startswith(parse_token + ':'):
        return [lines[first][len(parse_token + ':'):].strip()]
    elif lines[first].startswith(parse_token + 's:'):
        conditions = []
        for line in lines[first + 1:]:
            if line.startswith('-'):
                conditions.append(line[1:].strip())
            elif line != '':
                break
        return conditions
    else:
        return []


# @check_contracts
# def _my_sum(numbers: List[int]) -> int:
#     """Returns the sum of a list of numbers.
#
#     Preconditions:
#       - len(numbers) > 2
#       - numbers[0] == 3
#     """
#     return sum(numbers)
