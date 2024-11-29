"""Checker for a loop that can only ever run for one iteration.
"""

from typing import Union

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class OneIterationChecker(BaseChecker):
    name = "one_iteration"
    msgs = {
        "E9996": (
            "This loop will only ever run for one iteration",
            "one-iteration",
            "Reported when the loop body always ends the loop in its first iteration "
            '(e.g., by returning or using the "break" keyword).',
        )
    }
    options = (
        (
            "z3",
            {
                "default": False,
                "type": "yn",
                "metavar": "<y or n>",
                "help": "Use Z3 to restrict control flow checks to paths that are logically feasible.",
            },
        ),
    )

    @only_required_for_messages("one-iteration")
    def visit_for(self, node: nodes.For) -> None:
        """Visits for node"""
        if self._check_one_iteration(node):
            self.add_message("one-iteration", node=node)

    @only_required_for_messages("one-iteration")
    def visit_while(self, node: nodes.While) -> None:
        """Visits while node"""
        if self._check_one_iteration(node):
            self.add_message("one-iteration", node=node)

    def _check_one_iteration(self, node: Union[nodes.For, nodes.While]) -> bool:
        """Return whether the given loop is guaranteed to stop after one iteration.

        More precisely, Returns False if there exists a direct predecessor
        block `p` to the start of the loop block `s` such that the
        first statement in `p` is a child node of <node> and that there exists a
        path from `s` to `p.

        Note: For `while` loops, 'start of the loop block' refers to the block with
        the test condition (or the first of the blocks that make up test condition).
        For `for` loops, it refers to the block with the assignment target.
        """
        start = node.target if isinstance(node, nodes.For) else node
        if not hasattr(start, "cfg_block"):
            return False

        preds = start.cfg_block.predecessors

        if preds == []:
            return False

        if self.linter.config.z3:
            # check whether the loop statement is feasible
            if not start.cfg_block.is_feasible:
                return False
            # check whether the loop body is feasible (the loop has at least one iteration)
            if not any(
                succ.is_feasible and node.parent_of(succ.target.statements[0])
                for succ in start.cfg_block.successors
            ):
                return False
            # filter out unfeasible edges
            preds = [pred for pred in preds if pred.is_feasible]

        for pred in preds:
            stmt = pred.source.statements[0]
            if node.parent_of(stmt) and pred.source.reachable:
                if isinstance(node, nodes.For) and stmt is node.iter:
                    continue
                return False
        return True


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(OneIterationChecker(linter))
