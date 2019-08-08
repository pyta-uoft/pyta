from typing import Set, Generator, Tuple, Optional
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph, CFGBlock


def build_cfg(src: str, is_function: Optional[bool] = False) -> ControlFlowGraph:
    """<is_function> == True guarantees that the function node is the first node
    in the module."""
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    if is_function:
        return t.cfgs[mod.body[0]]
    return t.cfgs[mod]


def extract_blocks(cfg: ControlFlowGraph) -> Tuple[Set, Set]:
    """Returns (unreachable_set, reachable_set)"""
    reachable = (set(), set())
    for block in get_blocks(cfg.end):
        string = block.statements[0].as_string() if len(block.statements) > 0 else ''
        reachable[block.reachable].add(string)
    return reachable


def get_blocks(end_block: CFGBlock) -> Generator[CFGBlock, None, None]:
    """Generate a sequence of all blocks in this graph starting from the end up."""
    yield from _get_blocks(end_block, set())


def _get_blocks(block: CFGBlock,
                visited: Set[int]) -> Generator[CFGBlock, None, None]:
    if block.id in visited:
        return

    yield block
    visited.add(block.id)

    for edge in block.predecessors:
        yield from _get_blocks(edge.source, visited)


"""Note: The first statement of a block in the cfg of a test example cannot be 
the same as another block in the same cfg."""


def test_while_loop_simple() -> None:
    src = """
    while n > 10:
        print(n)
        break
        print(unreachable)
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'print(unreachable)'} == unreachable
    assert {'n > 10', 'print(n)', ''} == reachable


def test_while_loop_complex() -> None:
    src = """
    while n > 10:
        print(n)
        continue
        if n > 20:
            print(n - 1)
        else:
            print(5)
    print(outloop)
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'n > 20', 'print(n - 1)', 'print(5)'} == unreachable
    assert {'n > 10', 'print(n)', '', 'print(outloop)'} == reachable


def test_nested_while_loop() -> None:
    src = """
    while n > 10:
        if n > 20:
            break
            while x > 10:
                continue
                print(x - 1)
            else:
                print(x)
        else:
            print(n)
    print(outloop)
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'x > 10', 'print(x)', 'continue', 'print(x - 1)'} == unreachable
    assert {'n > 10', 'n > 20', '', 'print(n)', 'break', 'print(outloop)'} == reachable


def test_for_loop_simple() -> None:
    src = """
    for n in range(1, 10):
        print(n)
        break
        print(unreachable)
    print(outloop)
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'print(unreachable)'} == unreachable
    assert {'n', 'print(n)', '', 'range(1, 10)', 'print(outloop)'} == reachable


def test_for_loop_complex() -> None:
    src = """
    for n in range(1, 10):
        print(n)
        break
        if n > 20:
            print(n - 1)
        else:
            print(5)
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'n > 20', 'print(n - 1)', 'print(5)'} == unreachable
    assert {'n', 'range(1, 10)', '', 'print(n)'} == reachable


def test_nested_for_loop() -> None:
    src = """
    for n in range(1, 10):
        print(n)
        break
        for j in range(10):
            continue
    print(outloop)
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'j', 'range(10)', 'continue'} == unreachable
    assert {'n', 'range(1, 10)', '', 'print(n)', 'print(outloop)'} == reachable


def test_function_simple() -> None:
    src = """
    def func(n) -> None:
        return
        print(n)
    """
    cfg = build_cfg(src, is_function=True)
    unreachable, reachable = extract_blocks(cfg)
    assert {'print(n)'} == unreachable
    assert {'n', '', 'return'} == reachable


def test_function_complex() -> None:
    src = """
    def func(n) -> None:
        return
        for j in range(1, 10):
            continue
            print(j)
    """
    cfg = build_cfg(src, is_function=True)
    unreachable, reachable = extract_blocks(cfg)
    assert {'j', 'range(1, 10)', 'continue', 'print(j)'} == unreachable
    assert {'n', '', 'return'} == reachable


def test_while_with_if() -> None:
    src = """
    while n > 10:
        print(n)
        if n > 20:
            print('hi')
        else:
            break
            print('bye')
        print('after')
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'print(\'bye\')'} == unreachable
    assert {'n > 10', 'print(n)', '', 'print(\'hi\')', 'break', 'print(\'after\')'} == reachable


def test_while_with_if_complex() -> None:
    src = """
    while n > 10:
        print(n)
        if n > 20:
            print('hi')
        elif n > 25:
            continue
            print('unr')
        else:
            break
            print('bye')
        print('after')
    """
    cfg = build_cfg(src)
    unreachable, reachable = extract_blocks(cfg)
    assert {'print(\'bye\')', 'print(\'unr\')'} == unreachable
    assert {'n > 10', 'print(n)', '', 'print(\'hi\')', 'break', 'print(\'after\')',
            'continue', 'n > 25'} == reachable
