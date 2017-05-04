import astroid
import hypothesis.strategies as hs

# Custom strategies for hypothesis testing framework
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
    lambda: STRING,
])
INDEX_VALUES = INDEX_TYPES.flatmap(lambda s: s())

INTEGER = hs.integers()

STRING = hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1)

TUPLE =  (hs.lists(PRIMITIVE_VALUES, min_size=1)).map(tuple)

HOMO_LIST = PRIMITIVE_TYPES.flatmap(lambda s: hs.lists(s(), min_size=1))

HETERO_LIST = hs.lists(PRIMITIVE_VALUES, min_size=2)

HOMO_DICT = PRIMITIVE_TYPES.flatmap(lambda s: hs.dictionaries(s(), s(),  min_size=1))

HETERO_DICT = hs.dictionaries(PRIMITIVE_VALUES, PRIMITIVE_VALUES, min_size=2)



# Helper functions for testing
def _verify_type_setting(module, ast_class, expected_type):
    """Helper to verify nodes visited by type inference visitor of astroid class has been properly transformed."""
    result = [n.type_constraints.type for n in module.nodes_of_class(ast_class)]
    assert [expected_type] == result


def _verify_type_inf_child(module):
    """Helper to verify that AST node has the same type as it's value/child's"""
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type

def _index_input_formatter(var_input, index):
    """Helper to format input for testing index type inference visitor."""
    input_index = repr(var_input) + "[" + repr(index) + "]"
    return input_index