from __future__ import annotations

from typing import Union

# This creates a type alias, to save us typing "int | tuple[int, int]" everywhere
NodeAddress = Union[int, tuple[int, int]]


###############################################################################
# The Node class
###############################################################################
class Node:
    address: NodeAddress

    def __init__(self, address: NodeAddress) -> None:
        self.address = address


###############################################################################
# The AbstractNetwork class
###############################################################################
class AbstractNetwork:
    _nodes: dict[NodeAddress, Node]

    def __init__(self) -> None:
        self._nodes = {}
