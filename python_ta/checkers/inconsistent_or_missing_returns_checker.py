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
        # as R1710 is being disabled, we replace it with an identical message
        "R9710": (
            """This function has at least one case where the function body will execute without ending in an explicit return statement.
            You should check your code to make sure every possible execution path through the function body ends in a return statement.
            Note: one common source of this error is if you're using if statements without an explicit else branch.
            In this case, you should consider revising your code to either add an else branch,
            or, if you are confident that the if and elif conditions cover all possible cases,
            "you can convert the final "elif " into an " else ".",""",
            "inconsistent-returns",
            "Used to replace R1710 message inconsistent-return-statements",
        ),
        "R9711": (
            "Missing return statement in function",
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
        Construct a CFG from the function. Check for inconsistent returns if there are
        multiple return statements, and missing return statements if there are none.
        """
        if isinstance(node.returns, nodes.Const) and node.returns.value is None:
            return

        has_return_annotation = node.returns is not None
        any_branches_have_return = False

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
                    any_branches_have_return = True

        # check for inconsistent or missing returns
        if has_return_annotation or any_branches_have_return:
            for block in return_statements:
                statement = return_statements[block]
                if statement is None:
                    # for rendering purpose, the line is set to the last line of the function branch where return statement is missing
                    self.add_message(
                        "missing-return-statement", node=node, line=block.statements[-1].fromlineno
                    )
                elif statement.value is None:
                    self.add_message("inconsistent-returns", node=statement)


def register(linter: PyLinter) -> None:
    linter.register_checker(InconsistentReturnChecker(linter))
