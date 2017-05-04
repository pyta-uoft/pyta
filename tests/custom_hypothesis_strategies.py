import astroid
import hypothesis
import hypothesis.strategies as hs
from typing import Any, Dict, List, Tuple


PRIMITIVE_TYPES = hs.sampled_from([
    hs.integers,
    hs.booleans,
    lambda: hs.floats(allow_nan=False, allow_infinity=False),
    hs.none,
    hs.text,
])
PRIMITIVE_VALUES = PRIMITIVE_TYPES.flatmap(lambda s: s())

INDEX_TYPES = hs.sampled_from([
    hs.integers,
    lambda: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1),
])
INDEX_VALUES = INDEX_TYPES.flatmap(lambda s: s())

TUPLE =  (hs.lists(PRIMITIVE_VALUES, min_size=1)).map(tuple)

HOMO_LIST = PRIMITIVE_TYPES.flatmap(lambda s: hs.lists(s(), min_size=1))

HETERO_LIST = hs.lists(PRIMITIVE_VALUES, min_size=2)

HOMO_DICT = PRIMITIVE_TYPES.flatmap(lambda s: hs.dictionaries(s(), s(),  min_size=1))

HETERO_DICT = hs.dictionaries(PRIMITIVE_VALUES, PRIMITIVE_VALUES, min_size=2)

