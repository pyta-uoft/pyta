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
            "missing-return-statements",
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
        if (
            node.returns is None
            or isinstance(node.returns, nodes.Const)
            and node.returns.value is None
        ):
            return

        # get the end of CFG
        cfg = ControlFlowGraph()
        cfg.start = node.cfg_block
        end = [block for block in cfg.get_blocks_postorder()][0]
        end_blocks = [edge.source for edge in end.predecessors]

        # gather all return statements
        for block in end_blocks:
            has_return = False  # whether a return statement exists for this branch
            for statement in block.statements:
                if isinstance(statement, nodes.Return):
                    has_return = True
                    if statement.value is None:
                        # check for inconsistent returns
                        self.add_message("inconsistent-returns", node=statement)

            # check for missing return statement
            if not has_return:
                self.add_message("missing-return-statements", node=block.statements[-1])


def register(linter: PyLinter) -> None:
    linter.register_checker(InconsistentReturnChecker(linter))
