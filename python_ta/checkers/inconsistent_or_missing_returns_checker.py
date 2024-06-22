"""
Check for inconsistent return statements in functions and missing return statements in non-None functions.
"""

from typing import Optional

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.lint import PyLinter

from python_ta.cfg import ControlFlowGraph


class InconsistentReturnChecker(BaseChecker):

    name = "inconsistent-or-missing-returns"
    msgs = {
        "R9710": (
            """This function has inconsistent return statements: it sometimes returns a non-None value and sometimes uses `return` without a value.
            To ensure clarity and consistency, every return statement should either return a value or explicitly return None""",
            "inconsistent-returns",
            "Used when a function has non-None return values at some cases and `return` in other cases",
        ),
        "R9711": (
            "Missing return statement in function `%s`",
            "missing-return-statement",
            "Used when a function does not have a return statement and whose return type is not None",
        ),
    }

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter=linter)

    def visit_functiondef(self, node) -> None:
        """Visit a function definition"""
        self._check_return_statements(node)

    def _check_return_statements(self, node) -> None:
        """
        Check for inconsistent returns and missing returns based on CFG
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
                if return_statements[block].value is not None:
                    has_return_value = True

        # check for inconsistent or missing returns
        if has_return_annotation or has_return_value:
            for block in return_statements:
                statement = return_statements[block]
                if statement is None:
                    # for rendering purpose, the line is set to the last line of the function branch where return statement is missing
                    self.add_message(
                        "missing-return-statement",
                        node=node,
                        line=block.statements[-1].fromlineno,
                        args=node.name,
                    )
                elif statement.value is None:
                    self.add_message("inconsistent-returns", node=statement)


def register(linter: PyLinter) -> None:
    linter.register_checker(InconsistentReturnChecker(linter))
