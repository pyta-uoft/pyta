import astroid
import hypothesis.strategies as hs

# Custom strategies for hypothesis testing framework
primitive_types = hs.sampled_from([
    hs.integers,
    hs.booleans,
    lambda: hs.floats(allow_nan=False, allow_infinity=False),
    hs.none,
    hs.text,
])
primitive_values = primitive_types.flatmap(lambda s: s())

index_types = hs.sampled_from([
    hs.integers,
    lambda: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1)
])
index_values = index_types.flatmap(lambda s: s())

integer = hs.integers()

string = (lambda min, **kw: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=min, **kw))

tuple =  (hs.lists(primitive_values, min_size=1)).map(tuple)

homogeneous_list = primitive_types.flatmap(lambda s: hs.lists(s(), min_size=1))

random_list = hs.lists(primitive_values, min_size=2)

homogeneous_dictionary = primitive_types.flatmap(lambda s: hs.dictionaries(s(), s(),  min_size=1))

heterogeneous_dictionary = hs.dictionaries(primitive_values, primitive_values, min_size=2)


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