"""Checker for type inference errors.
"""

from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages

from python_ta.typecheck.base import TypeFail


class TypeInferenceChecker(BaseChecker):
    """A checker class that reports type errors"""

    name = "TypeInferenceChecker"
    msgs = {
        "E9900": (
            "Type error: %s",
            "type-error",
            "Presented when there is some kind of error with types.",
        )
    }

    @only_required_for_messages("type-error")
    def visit_default(self, node):
        if hasattr(node, "inf_type"):
            x = node.inf_type
            if isinstance(x, TypeFail):
                # If a child already has a type fail, this node inherited the
                # same one, so no need to report it again.
                for child in node.get_children():
                    if isinstance(getattr(child, "inf_type", None), TypeFail):
                        return

                # Otherwise, this is a new TypeFail that should be reported.
                self.add_message("type-error", args=x.msg, node=node)


def register(linter):
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(TypeInferenceChecker(linter))
