"""A checker for reporting on the disallowed use of various Python syntax.
"""
from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class ForbiddenPythonSyntaxChecker(BaseChecker):
    """A checker class to report on the disallowed use of various Python syntax.

    Includes checking the use of:
      - break
      - continue
      - comprehension
      - for
      - while
    """

    name = "forbidden_python_syntax"
    msgs = {
        "E9950": (
            "You may not use break statement(s).",
            "forbidden-break-usage",
            "Used when a break statement is found in your code.",
        ),
        "E9951": (
            "You may not use continue statement(s).",
            "forbidden-continue-usage",
            "Used when a continue statement is found in your code.",
        ),
        "E9952": (
            "You may not use any comprehensions.",
            "forbidden-comprehension-usage",
            "Used when a comprehension is found in your code.",
        ),
        "E9953": (
            "You may not use any for loops.",
            "forbidden-for-loop-usage",
            "Used when a for loop is found in your code.",
        ),
        "E9954": (
            "You may not use any while loops.",
            "forbidden-while-loop-usage",
            "Used when a while loop is found in your code.",
        ),
    }
    options = (
        (
            "allowed-python-syntax",
            {
                "default": (),
                "type": "csv",
                "metavar": "<allowed-syntax>",
                "help": "List of Python syntax that are allowed to be used.",
            },
        ),
    )

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("forbidden-break-usage")
    def visit_break(self, node: nodes.Break) -> None:
        """Visit a Break node."""
        if "break" not in self.linter.config.allowed_python_syntax:
            self.add_message("forbidden-break-usage", node=node)

    @only_required_for_messages("forbidden-continue-usage")
    def visit_continue(self, node: nodes.Continue) -> None:
        """Visit a Continue node."""
        if "continue" not in self.linter.config.allowed_python_syntax:
            self.add_message("forbidden-continue-usage", node=node)

    @only_required_for_messages("forbidden-comprehension-usage")
    def visit_comprehension(self, node: nodes.Comprehension) -> None:
        """Visit a Comprehension node."""
        if "comprehension" not in self.linter.config.allowed_python_syntax:
            self.add_message("forbidden-comprehension-usage", node=node)

    @only_required_for_messages("forbidden-for-loop-usage")
    def visit_for(self, node: nodes.For) -> None:
        """Visit a For node."""
        if "for" not in self.linter.config.allowed_python_syntax:
            self.add_message("forbidden-for-loop-usage", node=node)

    @only_required_for_messages("forbidden-while-loop-usage")
    def visit_while(self, node: nodes.While) -> None:
        """Visit a While node."""
        if "for" not in self.linter.config.allowed_python_syntax:
            self.add_message("forbidden-while-loop-usage", node=node)


def register(linter: PyLinter) -> None:
    """Register this checker to the linter."""
    linter.register_checker(ForbiddenPythonSyntaxChecker(linter))
