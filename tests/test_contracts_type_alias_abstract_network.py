from __future__ import annotations

from typing import Tuple

# This creates a type alias, to save us typing "Union[int, tuple]" everywhere
NodeAddress = Tuple[int, int]


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
