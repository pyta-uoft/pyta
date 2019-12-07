from typing import Any, List, Optional
import typing
import wrapt


@wrapt.decorator
def check_contracts(wrapped, _instance, args, kwargs):
    params = wrapped.__code__.co_varnames[:wrapped.__code__.co_argcount]
    annotations = typing.get_type_hints(wrapped)
    for arg, param in zip(args, params):
        if param in annotations:
            assert check_type_annotation(annotations[param], arg),\
                   f'Argument {repr(arg)} did not match type annotation for parameter "{param}: {annotations[param]}"'

    preconditions = parse_preconditions(wrapped.__doc__ or '')
    function_locals = dict(zip(params, args))
    for precondition in preconditions:
        try:
            check = eval(precondition, globals(), function_locals)
        except:
            # TODO: Decide what to do here, e.g. "Invalid precondition"
            pass
        else:
            assert check,\
                   f'Precondition "{precondition}" violated for arguments {function_locals}'
    r = wrapped(*args, **kwargs)
    if 'return' in annotations:
        return_type = annotations['return']
        assert check_type_annotation(return_type, r),\
            f'Return value {r} does not match annotated return type {return_type.__name__}'
    return r


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


def parse_preconditions(docstring: str) -> List[str]:
    """Return a list of preconditions parsed from the given docstring.

    Currently only supports two forms:

    1. A single line of the form "Precondition: <pre>"
    2. A group of lines starting with "Preconditions:", where each subsequent
       line is of the form "- <pre>". Each line is considered a separate precondition.
       The lines can be separated by blank lines, but no other text.
    """
    lines = [line.strip() for line in docstring.split('\n')]
    precondition_lines = [i
                          for i, line in enumerate(lines)
                          if line.lower().startswith('precondition')]

    if precondition_lines == []:
        return []

    first = precondition_lines[0]
    if lines[first].startswith('Precondition:'):
        return [lines[first][len('Precondition:'):].strip()]
    elif lines[first].startswith('Preconditions:'):
        preconditions = []
        for line in lines[first + 1:]:
            if line.startswith('-'):
                preconditions.append(line[1:].strip())
            elif line != '':
                break
        return preconditions
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
