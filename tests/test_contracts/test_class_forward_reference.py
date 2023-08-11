"""Tests for forward references in instance attribute type annotations."""
from __future__ import annotations

from typing import Any, Optional

import pytest

from python_ta.contracts import check_contracts


@check_contracts
class Node:
    """A node in a linked list."""

    item: Any
    next: Optional[Node]

    def __init__(self, item: Any) -> None:
        self.item = item
        self.next = None

    def bad_method(self) -> None:
        """Set self.next to an invalid value, violating the type annotation."""
        self.next = 1


def test_node_no_error() -> None:
    """Test that a Node can be initialized without error."""
    Node(1)


def test_node_setattr_no_error() -> None:
    """Test that assigning a valid attribute to a Node does not raise an error."""
    node = Node(1)
    node.next = Node(2)

    assert node.next.item == 2


def test_node_setattr_error() -> None:
    """Test that assigning an invalid attribute to a Node raises an AssertionError."""
    node = Node(1)

    with pytest.raises(AssertionError):
        node.next = 2


def test_node_method_error() -> None:
    """Test that violating a Node type annotation with a method call raises an AssertionError."""
    node = Node(1)

    with pytest.raises(AssertionError):
        node.bad_method()
