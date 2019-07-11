from python_ta.cfg.graph import ControlFlowGraph, CFGBlock
from python_ta.cfg.visitor import CFGVisitor
from astroid.builder import AstroidBuilder
from astroid.node_classes import NodeNG
from typing import Dict, Set, List, Generator, Tuple
import astroid


class DefiniteAssignmentAnalysis:
    _cfg_blocks: List[CFGBlock]
    _out: Dict[CFGBlock, Set[str]]
    _in: Dict[CFGBlock, Set[str]]

    # (key, value) = (variable name `v`, assignment node where `v` is a target)
    _assigns: Dict[str, NodeNG]

    def __init__(self, cfg: ControlFlowGraph) -> None:
        self._cfg_blocks = list(cfg.get_blocks())
        self._out, self._in = {}, {}
        self._assigns = dict()

    def analyze(self) -> List[NodeNG]:
        """Returns a list of astroid Assign nodes that might not be assigned."""
        pass

    def visit_cfg(self) -> None:
        """Traverses through CFG in a reverse post-order traversal."""
        all_assigns = self._get_assigns()
        for block in self._cfg_blocks:
            self._out[block] = all_assigns.copy()

        worklist = self._cfg_blocks[:]
        while len(worklist) != 0:
            b = worklist.pop()
            outs = [self._out[p.source] for p in b.predecessors]
            if outs == []:
                self._in[b] = set()
            else:
                self._in[b] = set.intersection(*outs)
            temp = self._in[b].union(self.gen(b))
            if temp != self._out[b]:
                self._out[b] = temp
                successors = set([succ.target for succ in b.successors])
                worklist = list(set(worklist).union(successors))

    def gen(self, block: CFGBlock) -> Set[str]:
        gen = set()
        for statement in block.statements:
            if isinstance(statement, astroid.Assign):
                for target in statement.targets:
                    gen.add(target.name)
            # if statement uses a variable that is not in either block.in or gen
            # then a variable might not be defined when this statement is executed.
        return gen

    def _extract_blocks(self) -> List[Tuple]:
        return [
            ([s.as_string() for s in block.statements], self._in[block], self._out[block])
            for block in self._cfg_blocks
        ]

    def _get_assigns(self) -> Set[str]:
        """Returns a set of all assignment statements."""
        assigns = set()
        for block in self._cfg_blocks:
            for statement in block.statements:
                if isinstance(statement, astroid.Assign):
                    for target in statement.targets:
                        assigns.add(target.name)
        return assigns


def get_cfgs(filename: str) -> CFGVisitor:
    mod = AstroidBuilder().file_build(filename)
    visitor = CFGVisitor()
    mod.accept(visitor)
    return visitor


if __name__ == '__main__':
    visitor = get_cfgs('cfg_misc.py')
    keys = list(visitor.cfgs)
    cfg = visitor.cfgs[keys[0]]
    analyzer = DefiniteAssignmentAnalysis(cfg)
    analyzer.visit_cfg()
    for blocks in analyzer._extract_blocks():
        print(blocks)
