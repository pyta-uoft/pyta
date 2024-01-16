import astroid
from astroid import nodes
from typing import TYPE_CHECKING, Optional

from pylint.checkers import BaseChecker

if TYPE_CHECKING:
    from pylint.lint import PyLinter


class NameLengthChecker(BaseChecker):
    name = "name-length"
    msgs = {
        "W0001": (
            "Name is too short. Invalid name on line %s",
            "minimum-name-length",
            "All variable names should be at least 5 characters.",
        ),
    }
    options = (
        (
            "ignore-names",
            {
                "default": False,
                "type": "yn",
                "metavar": "<y or n>",
                "help": "Allow any variable name length",
            },
        ),
    )

    def __init__(self, linter: Optional["PyLinter"] = None) -> None:
        super().__init__(linter)

    def visit_assign(self, node: nodes.Assign) -> None:
        for target in node.targets:
            if len(target.name) < 5 and not self.linter.config.ignore_names:
                self.add_message("minimum-name-length", node=node, args=(node.lineno,))


def register(linter: "PyLinter") -> None:
    """This required method auto registers the checker during initialization.
    :param linter: The linter to register the checker to.
    """
    linter.register_checker(NameLengthChecker(linter))
