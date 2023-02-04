"""A checker for reporting on the disallowed use of various Python syntax.
"""
from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class ForbiddenPythonSyntaxChecker(BaseChecker):
    """A checker class to report on the disallowed use of various Python syntax.

    Includes optional checking for the following syntax:
      - break
      - continue
      - comprehension
      - for
      - while

    By default, all Python syntax is allowed. Use options to disallow.
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
        name = _pascal_case_to_lower(node.__class__.__name__)

        if name in self.linter.config.disallowed_python_syntax:
            self.add_message("forbidden-python-syntax", node=node, args=name)

        return


def _pascal_case_to_lower(s: str) -> str:
    """Return the given string in lower case and separating each capitalized word with a space.

    Precondition:
      - s is a string in PascalCase and is the class name of an AST node.
    """
    out = ""

    for char in s:
        if char.isupper():
            out += " "
        out += char

    return out.lower().strip()


def register(linter: PyLinter) -> None:
    """Register this checker to the linter."""
    linter.register_checker(ForbiddenPythonSyntaxChecker(linter))
