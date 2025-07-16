"""Check for infinite while loops.

Note: Only checks if loop variable is reassigned for now."""

from typing import Generator, Optional

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
        "W9502": (
            "Usage of loops of the form 'while True' is discouraged",
            "while-true-loop",
            """Used when a 'while True' loop is detected and the configuration disallows it. This could lead to
            unintentionally infinite loops.""",
        ),
    }
    options = (
        (
            "allow-while-true",
            {
                "default": False,
                "type": "yn",
                "metavar": "<y or n>",
                "help": 'Allow infinite "while true" loops without raising a warning.',
            },
        ),
    )

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter=linter)

    def visit_while(self, node: nodes.While) -> None:
        self._check_condition_var_used(node)

    def leave_while(self, node: nodes.While) -> None:
        return

    def _check_condition_var_used(self, node: nodes.While) -> None:
        """Helper function that checks whether variables used in a while loop's condition
        are also used anywhere inside the loop body.

        Note: This is a basic check. It only flags loops where none of the condition variables
        appear in the body, which indicates an infinite loop.
        """
        # Get variable(s) used inside condition
        cond_vars = {}
        for child in node.test.nodes_of_class((nodes.Name, nodes.Attribute, nodes.Subscript)):
            if isinstance(child, nodes.Name) and child.name != "self":
                if cond_vars.get(child.name) is None:
                    cond_vars[child.name] = child
            elif isinstance(child, nodes.Attribute):
                if cond_vars.get(child.attrname) is None:
                    cond_vars[child.attrname] = child
            elif isinstance(child, nodes.Subscript):
                if cond_vars.get(child.value.name) is None:
                    cond_vars[child.value.name] = child
        if not cond_vars:
            if not self.linter.config.allow_while_true:
                self.add_message(
                    "while-true-loop",
                    node=node.test,
                    line=node.test.lineno,
                    end_lineno=node.test.end_lineno,
                )
            return

        # Check to see if condition variable(s) used inside body
        for child in node.body:
            for name_node in child.nodes_of_class((nodes.AssignName, nodes.AssignAttr)):
                if (
                    isinstance(name_node, nodes.AssignName)
                    and cond_vars.get(name_node.name) is not None
                    and isinstance(cond_vars[name_node.name], nodes.Name)
                ) or (
                    isinstance(name_node, nodes.AssignAttr)
                    and cond_vars.get(name_node.attrname) is not None
                    and isinstance(cond_vars[name_node.name], nodes.Attribute)
                ):
                    return

        else:
            self.add_message(
                "loop-condition-variable-unused",
                node=node,
                line=node.lineno,
                end_lineno=node.end_lineno,
            )
            return


def register(linter: PyLinter) -> None:
    linter.register_checker(InfiniteLoopChecker(linter))
