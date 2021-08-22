import os.path
from typing import Dict, Set

import graphviz
from astroid import nodes
from astroid.builder import AstroidBuilder

from python_ta.cfg import CFGBlock, CFGVisitor, ControlFlowGraph

USAGE = "USAGE: python -m sample_usage.draw_cfg <your-file.py>"
GRAPH_OPTIONS = {"format": "jpg", "node_attr": {"shape": "box", "fontname": "Courier New"}}


def display(cfgs: Dict[nodes.NodeNG, ControlFlowGraph], filename: str, view: bool = True) -> None:
    graph = graphviz.Digraph(name=filename, **GRAPH_OPTIONS)
    for node, cfg in cfgs.items():
        if isinstance(node, nodes.Module):
            subgraph_label = "__main__"
        elif isinstance(node, nodes.FunctionDef):
            subgraph_label = node.name
        else:
            continue
        with graph.subgraph(name=f"cluster_{id(node)}") as c:
            visited = set()
            _visit(cfg.start, c, visited)
            for block in cfg.unreachable_blocks:
                _visit(block, c, visited)
            c.attr(label=subgraph_label)

    graph.render(filename, view=view)


def _visit(block: CFGBlock, graph: graphviz.Digraph, visited: Set[int]) -> None:
    node_id = f"{graph.name}_{block.id}"
    if node_id in visited:
        return

    label = "\n".join([s.as_string() for s in block.statements]) + "\n"
    # Need to escape backslashes explicitly.
    label = label.replace("\\", "\\\\")
    # \l is used for left alignment.
    label = label.replace("\n", "\\l")

    fill_color = "grey93" if not block.reachable else "white"

    graph.node(node_id, label=label, fillcolor=fill_color, style="filled")
    visited.add(node_id)

    for edge in block.successors:
        graph.edge(node_id, f"{graph.name}_{edge.target.id}")
        _visit(edge.target, graph, visited)


def main(filepath: str) -> None:
    filename = os.path.splitext(os.path.basename(filepath))[0]
    mod = AstroidBuilder().file_build(filepath)
    visitor = CFGVisitor()
    mod.accept(visitor)

    display(visitor.cfgs, filename)


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print(USAGE)
        exit(1)

    filepath = sys.argv[1]
    main(filepath)
