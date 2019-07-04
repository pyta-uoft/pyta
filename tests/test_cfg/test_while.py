from typing import List, Tuple
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    return t.cfgs[mod]


def _extract_blocks(cfg: ControlFlowGraph) -> List[List[str]]:
    return [
        [s.as_string() for s in block.statements]
        for block in cfg.get_blocks()
    ]


def _extract_edges(cfg: ControlFlowGraph) -> List[List[List[str]]]:
    edges = [[edge.source.statements, edge.target.statements] for edge in cfg.get_edges()]
    expanded_edges = [[[source.as_string() for source in edge[0]],
                      [target.as_string() for target in edge[1]]]
                      for edge in edges]
    return expanded_edges


def test_simple_while_no_else() -> None:
    src = """
    while n > 10:
        print(n)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["n > 10"],
        ["print(n)"],
        []  # end block
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["print(n)"]],
        [["print(n)"], ["n > 10"]],
        [["n > 10"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_simple_while_with_else() -> None:
    src = """
    while n > 10:
        print(n)
    else:
        print(n + 1)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["n > 10"],
        ["print(n)"],
        ["print(n + 1)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["print(n)"]],
        [["print(n)"], ["n > 10"]],
        [["n > 10"], ["print(n + 1)"]],
        [["print(n + 1)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_simple_while_with_surrounding_blocks() -> None:
    src = """
    n = 10
    while n > 10:
        print(n - 1)
    else:
        print(n + 1)
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n = 10"],
        ["n > 10"],
        ["print(n - 1)"],
        ["print(n + 1)"],
        ["print(n)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n = 10"], ["n > 10"]],
        [["n > 10"], ["print(n - 1)"]],
        [["print(n - 1)"], ["n > 10"]],
        [["n > 10"], ["print(n + 1)"]],
        [["print(n + 1)"], ["print(n)"]],
        [["print(n)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_if() -> None:
    src = """
    while n > 10:
        if n > 20:
            print(y)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(y)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(y)"]],
        [["print(y)"], ["n > 10"]],
        [["n > 20"], ["n > 10"]],
        [["n > 10"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_if_and_statements() -> None:
    src = """
    while n > 10:
        if n > 20:
            print(y)
        print(k)
        print(j)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(y)"],
        ["print(k)", "print(j)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(y)"]],
        [["print(y)"], ["print(k)", "print(j)"]],
        [["print(k)", "print(j)"], ["n > 10"]],
        [["n > 20"], ["print(k)", "print(j)"]],
        [["n > 10"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_if_else() -> None:
    src = """
    while n > 10:
        if n > 20:
            print(y)
        else:
            print(j)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(y)"],
        ["print(j)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(y)"]],
        [["print(y)"], ["n > 10"]],
        [["n > 20"], ["print(j)"]],
        [["print(j)"], ["n > 10"]],
        [["n > 10"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_if_else_and_statements() -> None:
    src = """
    while n > 10:
        print(m)
        if n > 20:
            print(y)
        else:
            print(j)
        print(x)
        print(j)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["n > 10"],
        ["print(m)", "n > 20"],
        ["print(y)"],
        ["print(x)", "print(j)"],
        ["print(j)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["print(m)", "n > 20"]],
        [["print(m)", "n > 20"], ["print(y)"]],
        [["print(y)"], ["print(x)", "print(j)"]],
        [["print(x)", "print(j)"], ["n > 10"]],
        [["print(m)", "n > 20"], ["print(j)"]],
        [["print(j)"], ["print(x)", "print(j)"]],
        [["n > 10"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_break() -> None:
    src = """
    while n > 10:
        break
    else:
        print(n - 1)
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["break"],
        ["print(n)"],
        [],
        ["print(n - 1)"]
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["break"]],
        [["break"], ["print(n)"]],
        [["print(n)"], []],
        [["n > 10"], ["print(n - 1)"]],
        [["print(n - 1)"], ["print(n)"]]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_break_in_if() -> None:
    src = """
    while n > 10:
        if n > 20:
            print(n)
            break
        else:
            n -= 1
        print(n + 1)
    else:
        print(n - 1)
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(n)", "break"],
        ["print(n)"],
        [],
        ["n -= 1"],
        ["print(n + 1)"],
        ["print(n - 1)"],
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(n)", "break"]],
        [["print(n)", "break"], ["print(n)"]],
        [["print(n)"], []],
        [["n > 20"], ["n -= 1"]],
        [["n -= 1"], ["print(n + 1)"]],
        [["print(n + 1)"], ["n > 10"]],
        [["n > 10"], ["print(n - 1)"]],
        [["print(n - 1)"], ["print(n)"]],
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_break_in_if_else() -> None:
    src = """
        while n > 10:
            if n > 20:
                print(n)
            else:
                break
            n -= 1
        """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(n)"],
        ["n -= 1"],
        ["break"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(n)"]],
        [["print(n)"], ["n -= 1"]],
        [["n -= 1"], ["n > 10"]],
        [["n > 20"], ["break"]],
        [["break"], []],
        [["n > 10"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_nested_while() -> None:
    src = """
    while n > 10:
        while n > 20:
            print(n)
        else:
            print(n - 1)
    else:
        print(n + 1)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(n)"],
        ["print(n - 1)"],
        ["print(n + 1)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(n)"]],
        [["print(n)"], ["n > 20"]],
        [["n > 20"], ["print(n - 1)"]],
        [["print(n - 1)"], ["n > 10"]],
        [["n > 10"], ["print(n + 1)"]],
        [["print(n + 1)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_nested_while_with_break() -> None:
    src = """
    while n > 10:
        while n > 20:
            break
        print(n - 1)
        break
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["break"],
        ["print(n - 1)", "break"],
        ["print(n)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["break"]],
        [["break"], ["print(n - 1)", "break"]],
        [["print(n - 1)", "break"], ["print(n)"]],
        [["print(n)"], []],
        [["n > 20"], ["print(n - 1)", "break"]],
        [["n > 10"], ["print(n)"]]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_continue() -> None:
    src = """
    while n > 10:
        continue
    else:
        print(n - 1)
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["continue"],
        ["print(n - 1)"],
        ["print(n)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["continue"]],
        [["continue"], ["n > 10"]],
        [["n > 10"], ["print(n - 1)"]],
        [["print(n - 1)"], ["print(n)"]],
        [["print(n)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_continue_in_if() -> None:
    src = """
    while n > 10:
        if n > 20:
            print(n)
            continue
        else:
            n -= 1
        print(n + 1)
    else:
        print(n - 1)
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(n)", "continue"],
        ["n -= 1"],
        ["print(n + 1)"],
        ["print(n - 1)"],
        ["print(n)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(n)", "continue"]],
        [["print(n)", "continue"], ["n > 10"]],
        [["n > 20"], ["n -= 1"]],
        [["n -= 1"], ["print(n + 1)"]],
        [["print(n + 1)"], ["n > 10"]],
        [["n > 10"], ["print(n - 1)"]],
        [["print(n - 1)"], ["print(n)"]],
        [["print(n)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_continue_in_if_else() -> None:
    src = """
        while n > 10:
            if n > 20:
                print(n)
            else:
                continue
            n -= 1
        """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["print(n)"],
        ["n -= 1"],
        ["continue"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["print(n)"]],
        [["print(n)"], ["n -= 1"]],
        [["n -= 1"], ["n > 10"]],
        [["n > 20"], ["continue"]],
        [["continue"], ["n > 10"]],
        [["n > 10"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_nested_while_with_continue() -> None:
    src = """
    while n > 10:
        while n > 20:
            continue
        print(n - 1)
        continue
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["continue"],
        ["print(n - 1)", "continue"],
        ["print(n)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["continue"]],
        [["continue"], ["n > 20"]],
        [["n > 20"], ["print(n - 1)", "continue"]],
        [["print(n - 1)", "continue"], ["n > 10"]],
        [["n > 10"], ["print(n)"]],
        [["print(n)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_with_continue_break() -> None:
    src = """
    while n > 10:
        if n > 20:
            break
            print(unreachable)
        elif n > 25:
            continue
        print(k)
    print(n)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n > 10"],
        ["n > 20"],
        ["break"],
        ["print(n)"],
        [],
        ["n > 25"],
        ["continue"],
        ["print(k)"]
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n > 10"], ["n > 20"]],
        [["n > 20"], ["break"]],
        [["break"], ["print(n)"]],
        [["print(n)"], []],
        [["n > 20"], ["n > 25"]],
        [["n > 25"], ["continue"]],
        [["continue"], ["n > 10"]],
        [["n > 25"], ["print(k)"]],
        [["print(k)"], ["n > 10"]],
        [["n > 10"], ["print(n)"]]
    ]
    assert expected_edges == _extract_edges(cfg)
