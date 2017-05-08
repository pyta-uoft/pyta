import astroid
import hypothesis.strategies as hs
from typing import Any, Dict, List, Tuple

# Custom strategies for hypothesis testing framework
primitive_types = hs.sampled_from([
    hs.integers,
    hs.booleans,
    lambda: hs.floats(allow_nan=False, allow_infinity=False),
    hs.none,
    hs.text,
])
primitive_values = primitive_types.flatmap(lambda s: s())

# Strategies for generating Indexes
index_types = hs.sampled_from([
    hs.integers,
    lambda: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1)
])
index_values = index_types.flatmap(lambda s: s())


def tuple_strategy(**kwargs):
    """Return a strategy which generates a tuple."""
    return hs.lists(primitive_values, **kwargs).map(tuple)


def homogeneous_list(**kwargs):
    """Return a strategy which generates a list of uniform type."""
    return primitive_types.flatmap(lambda s: hs.lists(s(), **kwargs))


def random_list(**kwargs):
    """Return a strategy which generates a random list."""
    return hs.lists(primitive_values, **kwargs)


def homogeneous_dictionary(**kwargs):
    """Return a strategy which generates a dictionary of uniform key:value type."""
    return primitive_types.flatmap(lambda s: hs.dictionaries(s(), s(),  **kwargs))


def heterogeneous_dictionary(**kwargs):
    """Return a strategy which generates a dictionary of random key:value type."""
    return hs.dictionaries(index_values, primitive_values, **kwargs)


# Helper functions for testing
def _verify_type_setting(module, ast_class, expected_type):
    """Helper to verify nodes visited by type inference visitor of astroid class has been properly transformed."""
    result = [n.type_constraints.type for n in module.nodes_of_class(ast_class)]
    assert [expected_type] == result


def _verify_node_value_typematch(module):
    """Helper to verify that AST node has the same type as it's child's"""
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type


def _index_input_formatter(var_input, index):
    """Helper to format input for testing index type inference visitor."""
    return repr(var_input) + "[" + repr(index) + "]"
