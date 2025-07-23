"""Check for infinite while loops."""

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.lint import PyLinter


class InfiniteLoopChecker(BaseChecker):
    name = "infinite-loop"
    msgs = {
        "W9501": (
            "Infinite while loop: loop does not terminate",
            "infinite-loop",
            """Used when a while loop is guaranteed to never terminate based on its current structure. This usually
            indicates a logical error leading to an unintended infinite loop.""",
        ),
    }

    def visit_while(self, node: nodes.While) -> None:
        self._check_condition_all_var_used(node)

    def _check_condition_all_var_used(self, node: nodes.While) -> None:
        """Helper function that checks whether variables used in a while loop's condition
        are also used anywhere inside the loop body.

        Note: This is a basic check. It only flags loops where NONE of the condition variables
        appear in the body, which indicates an infinite loop.
        """
        # Get variable(s) used inside condition
        cond_vars = set(child.name for child in node.test.nodes_of_class(nodes.Name))
        # Remove function names
        for call in node.test.nodes_of_class(nodes.Call):
            if isinstance(call.func, nodes.Name) and call.func.name in cond_vars:
                cond_vars.remove(call.func.name)
        if not cond_vars:
            return
        # Check to see if condition variable(s) used inside body
        for child in node.body:
            for name_node in child.nodes_of_class((nodes.Name, nodes.AssignName)):
                if name_node.name in cond_vars:
                    # At least one condition variable is used in the loop body
                    return
        else:
            self.add_message(
                "infinite-loop",
                node=node.test,
            )


def register(linter: PyLinter) -> None:
    linter.register_checker(InfiniteLoopChecker(linter))
