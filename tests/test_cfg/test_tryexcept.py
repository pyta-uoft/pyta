from typing import List
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


def test_simple_tryexcept() -> None:
    src = """
    try:
        print(True)
    except Exception:
        pass
    """
    expected_blocks = [
        ['print(True)'],
        ['except Exception:', 'pass'],
        []  # end block
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks
