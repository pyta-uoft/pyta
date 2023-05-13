"""
Provides a method to generate and display the control flow graph of a given module.
"""
import importlib.util
import os.path
import sys
from typing import Dict, Optional, Set

import graphviz
from astroid import nodes
from astroid.builder import AstroidBuilder

from .graph import CFGBlock, ControlFlowGraph
from .visitor import CFGVisitor

GRAPH_OPTIONS = {"format": "svg", "node_attr": {"shape": "box", "fontname": "Courier New"}}
SUBGRAPH_OPTIONS = {"fontname": "Courier New"}


def generate_cfg(module_name: str = "", view: bool = True) -> None:
    """Generate a control flow graph for the given module.

    Args:
        module_name (str): The name of the module.
        view (bool): Open the control flow graph for viewing.

    The `module_name` can either be:
      - relative or absolute path of a file (must have `.py` extension).
      - no argument -- generate a CFG for the python file containing the function call.
    """
    _generate(module_name=module_name, view=view)


def _generate(module_name: str = "", view: bool = True) -> None:
    """Generate a control flow graph for the given module.

    The `module_name` can either be:
      - relative or absolute path of a file (must have `.py` extension).
      - no argument -- generate a CFG for the python file containing the function call.
    """
    # Generate a control flow graph for the given file
    abs_path = _get_valid_file_path(module_name)
    # Print an error message if the file is not valid and early return
    if abs_path is None:  # _get_valid_file_path returns None in case of invalid file
        return

    file_name = os.path.splitext(os.path.basename(abs_path))[0]
    mod = AstroidBuilder().file_build(abs_path)
    visitor = CFGVisitor()
    mod.accept(visitor)

    _display(visitor.cfgs, file_name, view=view)


def _get_valid_file_path(module_name: str = "") -> Optional[str]:
    """Return the valid absolute path of `module_name`, a relative path to the file."""
    # Allow call to check with empty args
    if module_name == "":
        m = sys.modules["__main__"]
        spec = importlib.util.spec_from_file_location(m.__name__, m.__file__)
        module_name = spec.origin
    # Enforce the API to only except `module_name` type as str
    elif not isinstance(module_name, str):
        print(
            "No CFG generated. Input to check, `{}`, has invalid type, must be a string.".format(
                module_name
            )
        )
        return

    # At this point, `module_name` is of type str
    if not os.path.isfile(module_name):
        # `module_name` is not a file so print an error message
        print("Could not find the file called, `{}`\n".format(module_name))
        return

    # `module_name` may be a relative path to a valid file so return its absolute path
    return os.path.abspath(module_name)


def _display(cfgs: Dict[nodes.NodeNG, ControlFlowGraph], filename: str, view: bool = True) -> None:
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
            _visit(cfg.start, c, visited, cfg.end)
            for block in cfg.unreachable_blocks:
                _visit(block, c, visited, cfg.end)
            c.attr(label=subgraph_label, **SUBGRAPH_OPTIONS)

    graph.render(filename, view=view)


def _visit(block: CFGBlock, graph: graphviz.Digraph, visited: Set[int], end: CFGBlock) -> None:
    """
    Visit a CFGBlock and add it to the control flow graph.
    """
    node_id = f"{graph.name}_{block.id}"
    if node_id in visited:
        return

    label = "\n".join([s.as_string() for s in block.statements]) + "\n"
    # Need to escape backslashes explicitly.
    label = label.replace("\\", "\\\\")
    # \l is used for left alignment.
    label = label.replace("\n", "\\l")

    fill_color = "grey93" if not block.reachable else "white"
    # Change the fill colour if block is the end of the cfg
    fill_color = "black" if block == end else fill_color

    graph.node(node_id, label=label, fillcolor=fill_color, style="filled")
    visited.add(node_id)

    for edge in block.successors:
        if edge.label is not None:
            graph.edge(node_id, f"{graph.name}_{edge.target.id}", str(edge.label))
        else:
            graph.edge(node_id, f"{graph.name}_{edge.target.id}")
        _visit(edge.target, graph, visited, end)
