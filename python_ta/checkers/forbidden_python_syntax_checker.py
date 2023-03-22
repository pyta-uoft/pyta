"""A checker for reporting on the disallowed use of various Python syntax.
"""
from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class ForbiddenPythonSyntaxChecker(BaseChecker):
    """A checker class to report on the disallowed use of various Python syntax.

    Use options to disallow specific types of Python syntax corresponding to astroid nodes,
    e.g. Break or For.
    """

    name = "forbidden_python_syntax"
    msgs = {
        "E9950": (
            "You may not use %s syntax in your code.",
            "forbidden-python-syntax",
            "Used when %s syntax is found in your code.",
        ),
    }
    options = (
        (
            "disallowed-python-syntax",
            {
                "default": (),
                "type": "csv",
                "metavar": "<disallowed-syntax>",
                "help": "List of Python syntax that are not allowed to be used.",
            },
        ),
    )

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("forbidden-python-syntax")
    def visit_default(self, node: nodes.NodeNG) -> None:
        """Visit a node in the AST."""
        name = node.__class__.__name__

        if name in self.linter.config.disallowed_python_syntax:
            self.add_message("forbidden-python-syntax", node=node, args=name)


def register(linter: PyLinter) -> None:
    """Register this checker to the linter."""
    linter.register_checker(ForbiddenPythonSyntaxChecker(linter))
