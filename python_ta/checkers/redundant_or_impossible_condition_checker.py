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


class RedundantOrImpossibleConditionChecker(BaseChecker):
    name = "redundant-condition"
    msgs = {
        "R9900": (
            """This conditional statement is already true given the preceding code;
             consider removing redundant check.""",
            "redundant-condition",
            "Used when an If or While statement is tautologically true based on preceding Z3 constraints."
            " Enabled when Z3 option is on.",
        ),
        "R9901": (
            """This conditional statement is never true given the preceding code.""",
            "impossible-condition",
            "Used when an If or While statement contradicts preceding Z3 constraints. Enable when Z3 option is on.",
        ),
    }
    options = (
        (
            "z3",
            {
                "default": False,
                "type": "yn",
                "metavar": "<y or n>",
                "help": "Use Z3 to perform logical feasibility analysis in program control flow.",
            },
        ),
    )

    def __init__(self, linter=None) -> None:
        super().__init__(linter=linter)

    @only_required_for_messages("redundant-condition", "impossible-condition")
    def visit_if(self, node: nodes.If) -> None:
        """Visit if statement"""
        self._check_condition(node)
        # handle else branch

    @only_required_for_messages("redundant-condition", "impossible-condition")
    def visit_while(self, node: nodes.While) -> None:
        """Visit while statement"""
        self._check_condition(node)

    def _check_condition(self, node: nodes.If | nodes.While) -> None:
        """A condition statement is redundant if for every feasible execution path
        leading to the node, the condition must be True by precedent constraints.
        """
        if (
            not hasattr(node, "cfg_block")
            or not z3_dependency_available
            or not self.linter.config.z3
        ):
            return

        node_block = node.cfg_block

        if not node_block.is_feasible or node_block.z3_constraint is None:
            return

        for pred in node_block.predecessors:
            if all(
                self._check_redundant_condition(
                    z3.And(*[c for c in constraints]), node_block.z3_constraint
                )
                for constraints in pred.z3_constraints.values()
            ):
                self.add_message("redundant-condition", node=node)
            if all(
                self._check_impossible_condition(
                    z3.And(*[c for c in constraints]), node_block.z3_constraint
                )
                for constraints in pred.z3_constraints.values()
            ):
                self.add_message("impossible-condition", node=node)

    def _check_redundant_condition(
        self, prev_constraints: z3.ExprRef, node_constraint: z3.ExprRef
    ) -> bool:
        """Check if the condition is redundant."""
        solver = z3.Solver()
        solver.add(z3.And(prev_constraints, node_constraint) != prev_constraints)
        return solver.check() == z3.unsat

    def _check_impossible_condition(
        self, prev_constraints: z3.ExprRef, node_constraint: z3.ExprRef
    ) -> bool:
        """Check if the condition is impossible."""
        solver = z3.Solver()
        solver.add(prev_constraints)
        solver.add(node_constraint)
        return solver.check() == z3.unsat


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter,
    Register the linter only if `z3` option is turned on.
    """
    linter.register_checker(RedundantOrImpossibleConditionChecker(linter))
