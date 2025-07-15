"""Check for infinite while loops.

Note: Only checks if loop variable is reassigned for now."""

from typing import Optional

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.lint import PyLinter


class InfiniteLoopChecker(BaseChecker):
    name = "infinite-loop"
    msgs = {
        "W9501": (
            "Loop variable in while condition is never updated inside the loop body",
            "loop-variable-not-updated",
            "Used when a loop variable in a while loop is never updated, which could lead to an infinite loop.",
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

    def visit_generic(self, node: nodes.NodeNG):
        for child in node.get_children():
            child.accept(self)

    def __getattr__(self, attr):
        if attr.startswith("visit_"):
            return self.visit_generic
        raise AttributeError(f"No attribute {attr}")

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter)
        self._inside_cond = False
        self._loop_cond_vars = []
        self._loop_body_vars = []

    def visit_module(self, module: nodes.Module) -> None:
        for child in module.body:
            # Check any classes or function definitions for the target function/method
            if isinstance(child, nodes.While):
                child.accept(self)

    def visit_while(self, node: nodes.While) -> None:
        # Visit loop condition nodes
        node.test.accept(self)

        # Visit loop body
        for child in node.body:
            child.accept(self)

    def leave_while(self, node: nodes.While) -> None:
        print(self._loop_cond_vars)
        print(self._loop_body_vars)
        self._loop_cond_vars = []
        self._loop_body_vars = []

    def visit_compare(self, node: nodes.Compare) -> None:
        self._inside_cond = True
        # Visit left hand side
        node.left.accept(self)
        # Visit rest of expression
        for operator, operand in node.ops:
            operand.accept(self)

    def leave_compare(self, node: nodes.Compare) -> None:
        self._inside_cond = False

    def visit_name(self, node: nodes.Name) -> None:
        if self._inside_cond and node.name not in self._loop_cond_vars:
            self._loop_cond_vars.append(node.name)
        return

    def visit_attribute(self, node: nodes.Attribute) -> None:
        if self._inside_cond and node.attrname not in self._loop_cond_vars:
            self._loop_cond_vars.append(node.attrname)
        return

    def visit_assign(self, node: nodes.Assign) -> None:
        for name in node.targets:
            name.accept(self)

    def visit_augassign(self, node: nodes.AugAssign) -> None:
        node.target.accept(self)

    def visit_assignattr(self, node: nodes.AssignAttr) -> None:
        if node.attrname not in self._loop_body_vars:
            self._loop_body_vars.append(node.attrname)

    def visit_assignname(self, node: nodes.AssignName) -> None:
        if node.name not in self._loop_body_vars:
            self._loop_body_vars.append(node.name)


def register(linter: PyLinter) -> None:
    linter.register_checker(InfiniteLoopChecker(linter))
