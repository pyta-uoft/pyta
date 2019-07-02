import astroid
from astroid.node_classes import NodeNG
from typing import Union, List
from python_ta.cfg import ControlFlowGraph, CFGBlock, CFGVisitor
import os
from astroid.builder import AstroidBuilder


def check_not_always_return(start: CFGBlock, loop: Union[astroid.For, astroid.While]) -> bool:
    """Returns True if there exists at least one predecessor block `p` to <start>
     block such that there exists a path from <start> to `p` where <start> is the
     start node of the path.

     <start> is the start block of a loop.
    """
    return any([_is_ancestor(pred.source.statements[-1], loop) for pred in start.predecessors])


def _is_ancestor(node: NodeNG, anstr: NodeNG) -> bool:
    """Returns True if <anstr> is an ancestor of <node>.

    Note: a node is an ancestor of itself.
    """
    if node == anstr:
        return True
    elif isinstance(node, astroid.Module):
        return False
    else:
        return _is_ancestor(node.parent, anstr)


def _get_loop_start(cfg: ControlFlowGraph) -> List[CFGBlock]:
    pass


def main(filepath: str) -> bool:
    filename = os.path.splitext(os.path.basename(filepath))[0]
    mod = AstroidBuilder().file_build(filepath)
    loop = mod.body[0]
    visitor = CFGVisitor()
    mod.accept(visitor)
    keys = list(visitor.cfgs)
    return check_not_always_return(visitor.cfgs[keys[0]].start, loop)


if __name__ == '__main__':
    print(main('cfg_misc.py'))


