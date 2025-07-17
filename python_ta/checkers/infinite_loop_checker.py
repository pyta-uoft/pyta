"""Check for infinite while loops."""

from typing import Optional

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.lint import PyLinter


class InfiniteLoopChecker(BaseChecker):
    name = "infinite-loop"
    msgs = {
        "W9501": (
            "No condition variable in the while loop is used inside the loop body",
            "loop-condition-variable-unused",
            """Used when none of the variables inside a while loop's condition appear in the body. This
            suggests the condition will never change and may result in an unintended infinite loop.""",
        ),
    }

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter=linter)

    def visit_while(self, node: nodes.While) -> None:
        self._check_condition_all_var_used(node)

    def leave_while(self, node: nodes.While) -> None:
        return

    def _check_condition_all_var_used(self, node: nodes.While) -> None:
        """Helper function that checks whether variables used in a while loop's condition
        are also used anywhere inside the loop body.

        Note: This is a basic check. It only flags loops where NONE of the condition variables
        appear in the body, which indicates an infinite loop.
        """
        # Get variable(s) used inside condition
        cond_vars = set()
        for child in node.test.nodes_of_class((nodes.Name, nodes.Attribute)):
            if isinstance(child, nodes.Name) and child.name != "self":
                cond_vars.add(child.name)
            else:
                # Avoid matching 'self.x' with local 'x' by using `as_string` method
                cond_vars.add(child.as_string())
        if not cond_vars:
            return
        # Check to see if condition variable(s) used inside body
        for child in node.body:
            for name_node in child.nodes_of_class(
                (nodes.AssignName, nodes.AssignAttr, nodes.Subscript)
            ):
                if (
                    isinstance(name_node, nodes.AssignName)
                    and name_node.name in cond_vars
                    or isinstance(name_node, nodes.AssignAttr)
                    and name_node.as_string() in cond_vars
                    or isinstance(name_node, nodes.Subscript)
                    and name_node.value.as_string() in cond_vars
                ):
                    # At least one condition variable is used in the loop body
                    return
        else:
            self.add_message(
                "loop-condition-variable-unused",
                node=node.test,
                line=node.test.lineno,
                end_lineno=node.test.end_lineno,
            )
            return


def register(linter: PyLinter) -> None:
    linter.register_checker(InfiniteLoopChecker(linter))
