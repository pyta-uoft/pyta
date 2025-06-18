"""
Check for inconsistent return statements in functions.
"""

from typing import Optional

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class InconsistentReturnChecker(BaseChecker):
    name = "inconsistent-returns"
    msgs = {
        "R9710": (
            """This function has inconsistent return statements: it sometimes returns a non-None value and sometimes uses `return` without a value.
            To ensure clarity and consistency, every return statement should either return a value or explicitly return None""",
            "inconsistent-returns",
            "Used when a function has non-None return values at some cases and `return` in other cases",
        ),
    }

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter=linter)

    @only_required_for_messages("inconsistent-returns")
    def visit_functiondef(self, node) -> None:
        """Visit a function definition"""
        self._check_return_statements(node)

    def _check_return_statements(self, node) -> None:
        """
        Check for inconsistent returns based on CFG
        if the function has a return type annotation or has at least one
        non-None return values.
        """
        if isinstance(node.returns, nodes.Const) and node.returns.value is None:
            return

        has_return_annotation = node.returns is not None
        has_return_value = False

        # get the blocks connected to the end of cfg
        end = node.cfg.end
        end_blocks = [edge.source for edge in end.predecessors]

        # gather the return statement of each code block
        return_statements = {}
        for block in end_blocks:
            return_statements[block] = None
            statement = block.statements[-1]
            if isinstance(statement, nodes.Return):
                return_statements[block] = statement
                # if the return statement is not `return` or `return None`
                if not (
                    statement.value is None
                    or isinstance(statement.value, nodes.Const)
                    and statement.value.value is None
                ):
                    has_return_value = True
            elif isinstance(statement, nodes.Raise):
                return_statements[block] = statement

        # check for inconsistent returns
        if has_return_annotation or has_return_value:
            for block, statement in return_statements.items():
                if isinstance(statement, nodes.Return) and statement.value is None:
                    self.add_message("inconsistent-returns", node=statement)


def register(linter: PyLinter) -> None:
    linter.register_checker(InconsistentReturnChecker(linter))
