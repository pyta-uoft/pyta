from __future__ import annotations
from typing import Generator, Optional, List, Set
from astroid.node_classes import NodeNG, Continue, Break, Return


class ControlFlowGraph:
    """A graph representing the control flow of a Python program."""
    start: CFGBlock
    end: CFGBlock
    # block_count is used as an "autoincrement" to ensure the block ids are unique.
    block_count: int

    def __init__(self) -> None:
        self.start = CFGBlock(0)
        self.end = CFGBlock(1)
        self.block_count = 2

    def create_block(self, pred: Optional[CFGBlock] = None) -> CFGBlock:
        """Create a new CFGBlock for this graph.

        If pred is specified, set that block as a predecessor of the new block.
        """
        new_block = CFGBlock(self.block_count)
        self.block_count += 1
        if pred:
            CFGEdge(pred, new_block)
        return new_block

    def link(self, source: CFGBlock, target: CFGBlock) -> None:
        """Link source to target."""
        CFGEdge(source, target)

    def link_or_merge(self, source: CFGBlock, target: CFGBlock) -> None:
        """Link source to target, or merge source into target if source is empty.

        An "empty" node for this purpose is when source has no statements.

        source with a jump statement cannot be further linked or merged to
        another target.
        """
        if source.is_jump():
            return
        if source.statements == []:
            if source is self.start:
                self.start = target
            else:
                for edge in source.predecessors:
                    edge.target = target
                    target.predecessors.append(edge)
        else:
            CFGEdge(source, target)

    def get_blocks(self) -> Generator[CFGBlock, None, None]:
        """Generate a sequence of all blocks in this graph."""
        yield from self._get_blocks(self.start, set())

    def _get_blocks(self, block: CFGBlock,
                    visited: Set[int]) -> Generator[CFGBlock, None, None]:
        if block.id in visited:
            return

        yield block
        visited.add(block.id)

        for edge in block.successors:
            yield from self._get_blocks(edge.target, visited)

    def get_edges(self) -> Generator[CFGEdge, None, None]:
        """Generate a sequence of all edges in this graph."""
        yield from self._get_edges(self.start, set())

    def _get_edges(self, block: CFGBlock,
                   visited: Set[int]) -> Generator[CFGEdge, None, None]:
        if block.id in visited:
            return

        visited.add(block.id)

        for edge in block.successors:
            yield edge
            yield from self._get_edges(edge.target, visited)


class CFGBlock:
    """A node in a control flow graph.

    Represents a maximal block of code whose statements are guaranteed to execute in sequence.
    """
    # A unique identifier
    id: int
    # The statements in this block.
    statements: List[NodeNG]
    # This block's in-edges (from blocks that can execute immediately before this one).
    predecessors: List[CFGEdge]
    # This block's out-edges (to blocks that can execute immediately after this one).
    successors: List[CFGEdge]

    def __init__(self, id_: int) -> None:
        """Initialize a new CFGBlock."""
        self.id = id_
        self.statements = []
        self.predecessors = []
        self.successors = []

    def add_statement(self, statement: NodeNG) -> None:
        if not self.is_jump():
            self.statements.append(statement)

    def is_jump(self) -> bool:
        """Returns True if the block has a statement that branches
        the control flow (ex: `break`)"""
        if len(self.statements) < 1:
            return False
        return isinstance(self.statements[-1], Break)


class CFGEdge:
    """An edge in a control flow graph.

    Edges are directed, and in the future may be augmented with auxiliary metadata about the control flow.
    """
    source: CFGBlock
    target: CFGBlock

    def __init__(self, source: CFGBlock, target: CFGBlock) -> None:
        self.source = source
        self.target = target
        self.source.successors.append(self)
        self.target.predecessors.append(self)
