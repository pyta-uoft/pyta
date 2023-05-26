import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.base import UpperCaseStyle
from pylint.checkers.base.name_checker.checker import DEFAULT_PATTERNS
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
                or _is_allowed_assignment(statement)
                or _is_main_block(statement)
            ):
                self.add_message("forbidden-top-level-code", node=statement, args=statement.lineno)


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


def _is_allowed_assignment(statement) -> bool:
    """
    Return whether or not <statement> is a constant assignment or type alias assignment.
    """
    if not isinstance(statement, nodes.Assign):
        return False

    names = []
    for target in statement.targets:
        names.extend(node.name for node in target.nodes_of_class(nodes.AssignName, nodes.Name))

    return all(
        re.match(UpperCaseStyle.CONST_NAME_RGX, name)
        or re.match(DEFAULT_PATTERNS["typealias"], name)
        for name in names
    )


def _is_main_block(statement) -> bool:
    """
    Return whether or not <statement> is the main block.
    """
    return (
        isinstance(statement, nodes.If)
        and isinstance(statement.test, nodes.Compare)
        and isinstance(statement.test.left, nodes.Name)
        and isinstance(statement.test.left, nodes.Name)
        and statement.test.left.name == "__name__"
        and len(statement.test.ops) == 1
        and statement.test.ops[0][0] == "=="
        and isinstance(statement.test.ops[0][1], nodes.Const)
        and statement.test.ops[0][1].value == "__main__"
    )


def register(linter):
    linter.register_checker(TopLevelCodeChecker(linter))
