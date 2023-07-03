from __future__ import annotations

from typing import Dict, Union

# This creates a type alias, to save us typing "Union[int, tuple]" everywhere
NodeAddress = Union[int, tuple]


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
    _nodes: Dict[NodeAddress, Node]

    def __init__(self) -> None:
        self._nodes = {}
