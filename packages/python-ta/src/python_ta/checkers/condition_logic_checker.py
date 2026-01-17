"""
Check for redundant/impossible If or While conditions in functions based on z3 constraints
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any, Union

from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages

if TYPE_CHECKING:
    from astroid import nodes
    from pylint.lint import PyLinter

    try:
        from z3 import ExprRef

    except ImportError:
        ExprRef = Any


class ConditionLogicChecker(BaseChecker):
    name = "redundant-condition"
    msgs = {
        "R9900": (
            """This condition will always evaluate to True.""",
            "redundant-condition",
            "Used when an If or While statement is always True. Requires the z3 configuration option to be True.",
        ),
        "R9901": (
            """This condition will always evaluate to False.""",
            "impossible-condition",
            "Used when an If or While statement is always False. Requires the z3 configuration option to be True.",
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

    @only_required_for_messages("redundant-condition", "impossible-condition")
    def visit_if(self, node: nodes.If) -> None:
        """Visit if statement"""
        self._check_condition(node)

    @only_required_for_messages("redundant-condition", "impossible-condition")
    def visit_while(self, node: nodes.While) -> None:
        """Visit while statement"""
        self._check_condition(node)

    def _check_condition(self, node: Union[nodes.If, nodes.While]) -> None:
        """Check whether a condition in an `if` or `while` statement is redundant
        or impossible based on the feasible execution paths.

        - A condition is redundant if for every feasible execution path
        leading to the node, the condition must be True due to precedent constraints.
        - A condition is impossible if for every feasible execution path
        leading to the node, the condition must be False due to precedent constraints.
        """
        if not hasattr(node, "cfg_block") or not self.linter.config.z3:
            return

        # Then z3 option is enabled
        try:
            import z3

            from ..cfg.graph import Z3Environment
        except ImportError:
            return

        node_block = node.cfg_block

        # create node condition z3 constraint
        condition_node = node.test
        env = Z3Environment(node.frame().cfg.z3_vars, [])
        z3_condition = env.parse_constraint(condition_node)

        if z3_condition is None:
            return

        if all(
            self._check_unsat(z3.And(*constraints), z3.Not(z3_condition))
            for edge in (pred for pred in node_block.predecessors if pred.is_feasible)
            for constraints in edge.z3_constraints.values()
        ):
            self.add_message("redundant-condition", node=node.test)

        if all(
            self._check_unsat(z3.And(*constraints), z3_condition)
            for edge in (pred for pred in node_block.predecessors if pred.is_feasible)
            for constraints in edge.z3_constraints.values()
        ):
            self.add_message("impossible-condition", node=node.test)

    def _check_unsat(self, prev_constraints: ExprRef, node_constraint: ExprRef) -> bool:
        """Check if the conjunction of the given constraints is unsatisfiable.

        - prev_constraints (z3.ExprRef): Constraints from previous nodes.
        - node_constraint (z3.ExprRef): The condition to check at the current node.
        """
        # z3 is already imported by caller (cached), no need to check for ImportError again
        import z3

        solver = z3.Solver()
        solver.add(z3.And(prev_constraints, node_constraint))
        return solver.check() == z3.unsat


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter."""
    linter.register_checker(ConditionLogicChecker(linter))
