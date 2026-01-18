"""Checker for index ranges"""

from astroid import nodes
from pylint.checkers import BaseChecker, utils
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class InvalidRangeIndexChecker(BaseChecker):
    """A checker class that reports the usage of an invalid index range."""

    name = "invalid_range_index"
    msgs = {
        "E9993": (
            "You should not use invalid range index on line %s",
            "invalid-range-index",
            "Used when you use invalid index range",
        )
    }

    @only_required_for_messages("invalid-range-index")
    def visit_call(self, node: nodes.Call) -> None:
        if isinstance(node.func, nodes.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()) and name == "range":
                args = node.args  # the arguments of 'range' call

                # ignore calls involving variables; these cannot be inferred properly
                if any(any(arg.nodes_of_class(nodes.Name)) for arg in args):
                    return

                inferred_params = [utils.safe_infer(arg) for arg in args]
                # Check whether every inference was successful
                if not all(isinstance(node, nodes.Const) for node in inferred_params):
                    return

                eval_params = [const.value for const in inferred_params]

                if (
                    len(args) == 0
                    or len(args) > 3
                    or not all([isinstance(c, int) for c in eval_params])
                ):
                    self.add_message("invalid-range-index", node=node, args=str(node.lineno))
                    return

                # set positional and default arguments of range
                start = eval_params[0] if len(args) > 1 else 0
                stop = eval_params[0] if len(args) == 1 else eval_params[1]
                step = eval_params[2] if len(args) == 3 else 1

                if not is_valid_range(start, stop, step):
                    self.add_message("invalid-range-index", node=node, args=str(node.lineno))


def is_valid_range(start: int, stop: int, step: int) -> bool:
    """Returns True if a range call with three arguments is valid.
    We consider a range to be valid if it has more than one element."""
    if step == 0:
        return False
    return (stop - start) / step > 1


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(InvalidRangeIndexChecker(linter))
