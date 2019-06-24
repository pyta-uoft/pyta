import os.path
from typing import Set
from astroid.builder import AstroidBuilder
import graphviz
from python_ta.cfg import CFGVisitor, ControlFlowGraph, CFGBlock


USAGE = 'USAGE: python -m sample_usage.draw_cfg <your-file.py>'
GRAPH_OPTIONS = {
    'format': 'jpg',
    'node_attr': {
        'shape': 'box',
        'fontname': 'Courier New'
    }
}


def display(cfg: ControlFlowGraph, filename: str, view: bool = True) -> None:
    graph = graphviz.Digraph(name=filename, **GRAPH_OPTIONS)
    _visit(cfg, cfg.start, graph, set())
    graph.render(filename, view=view)


def _visit(cfg: ControlFlowGraph, block: CFGBlock,
           graph: graphviz.Digraph, visited: Set[int]) -> None:
    if block.id in visited:
        return

    label = '\l'.join([s.as_string() for s in block.statements])
    graph.node(str(block.id), label=label)
    visited.add(block.id)

    for edge in block.successors:
        graph.edge(str(block.id), str(edge.target.id))
        _visit(cfg, edge.target, graph, visited)


def main(filepath: str) -> None:
    filename = os.path.splitext(os.path.basename(filepath))[0]
    mod = AstroidBuilder().file_build(filepath)
    visitor = CFGVisitor()
    mod.accept(visitor)

    display(visitor.cfgs[mod], filename)


if __name__ == '__main__':
    import sys
    if len(sys.argv) < 2:
        print(USAGE)
        exit(1)

    filepath = sys.argv[1]
    main(filepath)
