import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages

from python_ta.utils import _is_in_main


class TopLevelCodeChecker(BaseChecker):
    name = "Top_Level_Code"
    msgs = {
        "E9992": (
            "You may not write top level code %s",
            "forbidden-top-level-code",
            "Used when you write top-level code that is not allowed. "
            "The allowed top-level code includes imports, definitions, and assignments.",
        )
    }

    # this is important so that your checker is executed before others
    priority = -1

    @only_required_for_messages("forbidden-top-level-code")
    def visit_module(self, node):
        if (
            not _is_import(node)
            and not _is_definition(node)
            and not _is_constant_assignment(node)
            and not _is_in_main(node)
        ):
            body = node.body
            self.add_message("forbidden-top-level-code", node=node, args=body)


# Helper functions
def _is_import(node):
    for statement in node.body:
        if isinstance(statement, nodes.Import) or isinstance(statement, nodes.ImportFrom):
            return True
    return False


def _is_definition(node):
    for statement in node.body:
        if isinstance(statement, nodes.FunctionDef) or isinstance(statement, nodes.ClassDef):
            return True
    return False


def _is_constant_assignment(node):
    for statement in node.body:
        if isinstance(statement, nodes.Assign) and re.search(
            "^[A-Z]+(?:_[A-Z]+)*$", statement.targets[0].name
        ):
            return True
    return False


def register(linter):
    linter.register_checker(TopLevelCodeChecker(linter))
