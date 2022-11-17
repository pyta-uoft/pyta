import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.base import UpperCaseStyle
from pylint.checkers.utils import only_required_for_messages


class TopLevelCodeChecker(BaseChecker):
    name = "top_level_code"
    msgs = {
        "E9992": (
            "Forbidden top-level code found on line %s",
            "forbidden-top-level-code",
            "Used when you write top-level code that is not allowed. "
            "The allowed top-level code includes imports, definitions, and assignments.",
        )
    }

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("forbidden-top-level-code")
    def visit_module(self, node):
        for statement in node.body:
            if not (
                _is_import(statement)
                or _is_definition(statement)
                or _is_constant_assignment(statement)
                or _is_main_block(statement)
            ):
                self.add_message("forbidden-top-level-code", node=node, args=statement.lineno)


# Helper functions
def _is_import(statement) -> bool:
    """
    Return whether or not <statement> is an Import or an ImportFrom.
    """
    return isinstance(statement, (nodes.Import, nodes.ImportFrom))


def _is_definition(statement) -> bool:
    """
    Return whether or not <statement> is a function definition or a class definition.
    """
    return isinstance(statement, (nodes.FunctionDef, nodes.ClassDef))


def _is_constant_assignment(statement) -> bool:
    """
    Return whether or not <statement> is a constant assignment.
    """
    return isinstance(statement, nodes.Assign) and re.match(
        UpperCaseStyle.CONST_NAME_RGX, statement.targets[0].name
    )


def _is_main_block(statement) -> bool:
    """
    Return whether or not <statement> is the main block.
    """
    return (
        isinstance(statement, nodes.If)
        and statement.test.left.name == "__name__"
        and statement.test.ops[0][1].value == "__main__"
    )


def register(linter):
    linter.register_checker(TopLevelCodeChecker(linter))
