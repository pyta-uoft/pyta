"""
Check for redundant If or While conditions in functions based on z3 constraints
"""

from typing import Any

try:
    import z3

    z3_dependency_available = True
except ImportError:
    z3 = Any
    z3_dependency_available = False

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class RedundantConditionChecker(BaseChecker):
    name = "redundant-condition"
    msgs = {
        "R9900": (
            """Condition is already true given the preceding code; consider removing redundant check.""",
            "redundant-condition",
            "Used when an If and While statements is tautologically true based on preceding Z3 constraints."
            " Enabled when Z3 option is on.",
        ),
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

    def __init__(self, linter=None) -> None:
        super().__init__(linter=linter)

    @only_required_for_messages("redundant-condition")
    def visit_if(self, node: nodes.If) -> None:
        """Visit if statement"""
        if self._check_redundant_condition(node):
            self.add_message("redundant-condition", node=node)

    @only_required_for_messages("redundant-condition")
    def visit_while(self, node: nodes.While) -> None:
        """Visit while statement"""
        if self._check_redundant_condition(node):
            self.add_message("redundant-condition", node=node)

    def _check_redundant_condition(self, node: nodes.If | nodes.While) -> bool:
        """A condition statement is redundant if for every feasible execution path
        leading to the node, the condition must be True by precedent constraints
        """
        if not z3_dependency_available or not hasattr(node, "cfg_block"):
            return False

        node_block = node.cfg_block

        if not node_block.is_feasible or node_block.z3_constraint is None:
            return False

        solver = z3.Solver()
        for pred in node_block.predecessors:
            for constraints in pred.z3_constraints.values():
                solver.push()
                prev_constraints = z3.And(*[c for c in constraints])
                solver.add(z3.And(node_block.z3_constraint, prev_constraints) != prev_constraints)
                if solver.check() == z3.sat:
                    return False
                solver.pop()

        return True


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter,
    Register the linter only if `z3` option is turned on.
    """
    if linter.config.z3:
        linter.register_checker(RedundantConditionChecker(linter))
