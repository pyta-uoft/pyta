import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages


class TopLevelCodeChecker(BaseChecker):
    name = "Top_Level_Code"
    msgs = {
        "E9992": (
            "Forbidden top level code found on line %s",
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
            if (
                not _is_import(statement)
                and not _is_definition(statement)
                and not _is_constant_assignment(statement)
                and not _is_main(statement)
            ):
                self.add_message("forbidden-top-level-code", node=node, args=statement.lineno)


# Helper functions
def _is_import(statement):
    if isinstance(statement, nodes.Import) or isinstance(statement, nodes.ImportFrom):
        return True
    return False


def _is_definition(statement):
    if isinstance(statement, nodes.FunctionDef) or isinstance(statement, nodes.ClassDef):
        return True
    return False


def _is_constant_assignment(statement):
    if isinstance(statement, nodes.Assign) and re.search(
        "^[A-Z]+(?:_[A-Z]+)*$", statement.targets[0].name
    ):
        return True
    return False


def _is_main(statement):
    if (
        isinstance(statement, nodes.If)
        and statement.test.left.name == "__name__"
        and statement.test.ops[0][1].value == "__main__"
    ):
        return True
    return False


def register(linter):
    linter.register_checker(TopLevelCodeChecker(linter))
