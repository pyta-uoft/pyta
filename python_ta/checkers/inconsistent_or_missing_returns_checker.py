"""
Check for inconsistent return statements in functions and missing return statements in non-None functions.
"""

from typing import Optional, Set

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


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

    @only_required_for_messages("missing-return-statement", "inconsistent-returns")
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
                end_lines = self._search_for_end_line(block, set())
                if statement is None:
                    """
                    For rendering purpose:
                    line: the line where the error occurs, used to calculate indentation
                    end_line: the line to insert the error message
                    """
                    self.add_message(
                        "missing-return-statement",
                        node=node,
                        line=block.statements[-1].tolineno,
                        end_lineno=max((line for line in end_lines)),
                        args=node.name,
                    )
                elif statement.value is None:
                    self.add_message("inconsistent-returns", node=statement)

    def _search_for_end_line(self, block, visited: Set[int]):
        """
        Recursively search for the line number of the end of a nested block
        """
        if block.id in visited or block.id == 1:
            return

        visited.add(block.id)
        end = block.statements[-1].lineno
        # the only successors are end block or visited
        if all(
            successor.target.id == 1 or successor.target.id in visited
            for successor in block.successors
        ):
            yield end
        else:
            for successor in block.successors:
                yield from self._search_for_end_line(successor.target, visited)

        visited.remove(block.id)


def register(linter: PyLinter) -> None:
    linter.register_checker(InconsistentReturnChecker(linter))
