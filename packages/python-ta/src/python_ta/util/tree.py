"""
Simple Tree class to be used for RecursionTable.
"""

from __future__ import annotations

from typing import Any


class Tree:
    """
    This class is used by RecursionTable to represent a
    recursive call.

    Instance attributes:
        value: the value of the tree node
        children: the child nodes of the tree
    """

    value: Any
    children: list[Tree]

    def __init__(self, value: Any) -> None:
        """Initialize a Tree with no children by default."""
        self.value = value
        self.children = []

    def add_child(self, child_node: Tree) -> None:
        """Add child_node as one of the tree's children."""
        self.children.append(child_node)

    def __eq__(self, tree: Tree) -> bool:
        """Check if self and tree are equal by comparing their values and
        structure.
        """
        if self.value != tree.value or len(self.children) != len(tree.children):
            return False
        for i in range(len(self.children)):
            if not self.children[i].__eq__(tree.children[i]):
                return False
        return True
