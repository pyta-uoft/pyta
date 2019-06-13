from typing import List
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    return t.cfg


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


def test_simple_for_no_else() -> None:
    src = """
    for i in range(10):
        print(i)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["i", "range(10)"],
        ["print(i)"],
        []  # end block
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["print(i)"]],
        [["print(i)"], ["i", "range(10)"]],
        [["i", "range(10)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_simple_for_two_targ() -> None:
    src = """
    for i, j in zip(range(10), range(20)):
        print(i, j)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["(i, j)", "zip(range(10), range(20))"],
        ["print(i, j)"],
        []  # end block
    ]
    print(_extract_blocks(cfg))
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["(i, j)", "zip(range(10), range(20))"], ["print(i, j)"]],
        [["print(i, j)"], ["(i, j)", "zip(range(10), range(20))"]],
        [["(i, j)", "zip(range(10), range(20))"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_simple_for_with_else() -> None:
    src = """
    for i in range(10):
        print(i)
    else:
        print(i + 1)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["i", "range(10)"],
        ["print(i)"],
        ["print(i + 1)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["print(i)"]],
        [["print(i)"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i + 1)"]],
        [["print(i + 1)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_simple_for_with_surrounding_blocks() -> None:
    src = """
    n = 10
    for i in range(n):
        print(i - 1)
    else:
        print(i + 1)
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["n = 10"],
        ["i", "range(n)"],
        ["print(i - 1)"],
        ["print(i + 1)"],
        ["print(i)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["n = 10"], ["i", "range(n)"]],
        [["i", "range(n)"], ["print(i - 1)"]],
        [["print(i - 1)"], ["i", "range(n)"]],
        [["i", "range(n)"], ["print(i + 1)"]],
        [["print(i + 1)"], ["print(i)"]],
        [["print(i)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_if() -> None:
    src = """
    for i in range(10):
        if i > 5:
            print(y)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(y)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(y)"]],
        [["print(y)"], ["i", "range(10)"]],
        [["i > 5"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_if_and_statements() -> None:
    src = """
    for i in range(10):
        if i > 5:
            print(y)
        print(k)
        print(j)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(y)"],
        ["print(k)", "print(j)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(y)"]],
        [["print(y)"], ["print(k)", "print(j)"]],
        [["print(k)", "print(j)"], ["i", "range(10)"]],
        [["i > 5"], ["print(k)", "print(j)"]],
        [["i", "range(10)"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_if_else() -> None:
    src = """
    for i in range(10):
        if i > 5:
            print(y)
        else:
            print(j)
    else:
        print(x)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(y)"],
        ["print(j)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(y)"]],
        [["print(y)"], ["i", "range(10)"]],
        [["i > 5"], ["print(j)"]],
        [["print(j)"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_if_else_and_statements() -> None:
    src = """
    for i in range(10):
        print(m)
        if i > 5:
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
        ["i", "range(10)"],
        ["print(m)", "i > 5"],
        ["print(y)"],
        ["print(x)", "print(j)"],
        ["print(j)"],
        ["print(x)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["print(m)", "i > 5"]],
        [["print(m)", "i > 5"], ["print(y)"]],
        [["print(y)"], ["print(x)", "print(j)"]],
        [["print(x)", "print(j)"], ["i", "range(10)"]],
        [["print(m)", "i > 5"], ["print(j)"]],
        [["print(j)"], ["print(x)", "print(j)"]],
        [["i", "range(10)"], ["print(x)"]],
        [["print(x)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_break() -> None:
    src = """
    for i in range(10):
        break
    else:
        print(i - 1)
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["break"],
        ["print(i)"],
        [],
        ["print(i - 1)"]
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["break"]],
        [["break"], ["print(i)"]],
        [["print(i)"], []],
        [["i", "range(10)"], ["print(i - 1)"]],
        [["print(i - 1)"], ["print(i)"]]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_break_in_if() -> None:
    src = """
    for i in range(10):
        if i > 5:
            print(i)
            break
        else:
            i -= 1
        print(i + 1)
    else:
        print(i - 1)
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(i)", "break"],
        ["print(i)"],
        [],
        ["i -= 1"],
        ["print(i + 1)"],
        ["print(i - 1)"],
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(i)", "break"]],
        [["print(i)", "break"], ["print(i)"]],
        [["print(i)"], []],
        [["i > 5"], ["i -= 1"]],
        [["i -= 1"], ["print(i + 1)"]],
        [["print(i + 1)"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i - 1)"]],
        [["print(i - 1)"], ["print(i)"]],
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_break_in_if_else() -> None:
    src = """
        for i in range(10):
            if i > 5:
                print(i)
            else:
                break
            i -= 1
        """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(i)"],
        ["i -= 1"],
        ["break"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(i)"]],
        [["print(i)"], ["i -= 1"]],
        [["i -= 1"], ["i", "range(10)"]],
        [["i > 5"], ["break"]],
        [["break"], []],
        [["i", "range(10)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_nested_for() -> None:
    src = """
    for i in range(10):
        for i in range(5):
            print(i)
        else:
            print(i - 1)
    else:
        print(i + 1)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i", "range(5)"],
        ["print(i)"],
        ["print(i - 1)"],
        ["print(i + 1)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i", "range(5)"]],
        [["i", "range(5)"], ["print(i)"]],
        [["print(i)"], ["i", "range(5)"]],
        [["i", "range(5)"], ["print(i - 1)"]],
        [["print(i - 1)"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i + 1)"]],
        [["print(i + 1)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_nested_for_with_break() -> None:
    src = """
    for i in range(10):
        for i in range(5):
            break
        print(i - 1)
        break
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i", "range(5)"],
        ["break"],
        ["print(i - 1)", "break"],
        ["print(i)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i", "range(5)"]],
        [["i", "range(5)"], ["break"]],
        [["break"], ["print(i - 1)", "break"]],
        [["print(i - 1)", "break"], ["print(i)"]],
        [["print(i)"], []],
        [["i", "range(5)"], ["print(i - 1)", "break"]],
        [["i", "range(10)"], ["print(i)"]]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_continue() -> None:
    src = """
    for i in range(10):
        continue
    else:
        print(i - 1)
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["continue"],
        ["print(i - 1)"],
        ["print(i)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["continue"]],
        [["continue"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i - 1)"]],
        [["print(i - 1)"], ["print(i)"]],
        [["print(i)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_continue_in_if() -> None:
    src = """
    for i in range(10):
        if i > 5:
            print(i)
            continue
        else:
            i -= 1
        print(i + 1)
    else:
        print(i - 1)
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(i)", "continue"],
        ["i -= 1"],
        ["print(i + 1)"],
        ["print(i - 1)"],
        ["print(i)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(i)", "continue"]],
        [["print(i)", "continue"], ["i", "range(10)"]],
        [["i > 5"], ["i -= 1"]],
        [["i -= 1"], ["print(i + 1)"]],
        [["print(i + 1)"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i - 1)"]],
        [["print(i - 1)"], ["print(i)"]],
        [["print(i)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_continue_in_if_else() -> None:
    src = """
        for i in range(10):
            if i > 5:
                print(i)
            else:
                continue
            i -= 1
        """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["print(i)"],
        ["i -= 1"],
        ["continue"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["print(i)"]],
        [["print(i)"], ["i -= 1"]],
        [["i -= 1"], ["i", "range(10)"]],
        [["i > 5"], ["continue"]],
        [["continue"], ["i", "range(10)"]],
        [["i", "range(10)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_nested_for_with_continue() -> None:
    src = """
    for i in range(10):
        for i in range(5):
            continue
        print(i - 1)
        continue
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i", "range(5)"],
        ["continue"],
        ["print(i - 1)", "continue"],
        ["print(i)"],
        []
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i", "range(5)"]],
        [["i", "range(5)"], ["continue"]],
        [["continue"], ["i", "range(5)"]],
        [["i", "range(5)"], ["print(i - 1)", "continue"]],
        [["print(i - 1)", "continue"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i)"]],
        [["print(i)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_for_with_continue_break() -> None:
    src = """
    for i in range(10):
        if i > 5:
            break
            print(unreachable)
        elif i > 2:
            continue
        print(k)
    print(i)
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ["i", "range(10)"],
        ["i > 5"],
        ["break"],
        ["print(i)"],
        [],
        ["i > 2"],
        ["continue"],
        ["print(k)"]
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["i", "range(10)"], ["i > 5"]],
        [["i > 5"], ["break"]],
        [["break"], ["print(i)"]],
        [["print(i)"], []],
        [["i > 5"], ["i > 2"]],
        [["i > 2"], ["continue"]],
        [["continue"], ["i", "range(10)"]],
        [["i > 2"], ["print(k)"]],
        [["print(k)"], ["i", "range(10)"]],
        [["i", "range(10)"], ["print(i)"]]
    ]
    assert expected_edges == _extract_edges(cfg)
