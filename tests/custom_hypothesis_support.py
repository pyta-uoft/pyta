import astroid
import hypothesis.strategies as hs
from hypothesis import assume
from python_ta.transforms.type_inference_visitor import register_type_constraints_setter,\
    environment_transformer
from keyword import iskeyword
from python_ta.transforms.type_inference_visitor import TYPE_CONSTRAINTS
from hypothesis import settings
settings.register_profile("pyta", settings(max_examples=10))

# Custom strategies for hypothesis testing framework
primitive_types = hs.sampled_from([
    hs.integers,
    hs.booleans,
    lambda: hs.floats(allow_nan=False, allow_infinity=False),
    hs.none,
    hs.text,
    hs.binary
])
primitive_values = primitive_types.flatmap(lambda s: s())


# Strategies for generating Indexes
index_types = hs.sampled_from([
    hs.integers,
    lambda: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1)
])
index_values = index_types.flatmap(lambda s: s())


# Strategies for generating Binary Operators
non_bool_symbols = ['+', '-', '*', '//', '%', '/', '**', '&', '^', '~', '|', '<<', '>>']
non_boolean_operator = hs.sampled_from(non_bool_symbols)
non_bool_unary_op = hs.sampled_from(['-', '+', '~'])


# Strategy for generating Boolean Operators
binary_bool_operator = hs.sampled_from(['and', 'or'])
unary_bool_operator = hs.sampled_from(['not'])


def valid_identifier():
    """Return a strategy which generates a valid Python Identifier"""
    return hs.text(alphabet="abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789", min_size=1)\
        .filter(lambda x: x[0].isalpha() and x.isidentifier() and not (iskeyword(x)))


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


def random_dict_variable_value(**kwargs):
    """Return a strategy which generates a random dictionary of variable name and value"""
    return primitive_types.flatmap(lambda s: hs.dictionaries(valid_identifier(), s(), **kwargs))


def heterogeneous_dictionary(**kwargs):
    """Return a strategy which generates a dictionary of random key:value type."""
    return hs.dictionaries(index_values, primitive_values, **kwargs)


# Helper functions for testing
def _parse_text(source: str) -> astroid.Module:
    """Parse source code text and output an AST with type inference performed."""
    TYPE_CONSTRAINTS.clear_tvars()
    module = astroid.parse(source)
    environment_transformer().visit(module)
    register_type_constraints_setter().visit(module)
    return module


def _verify_type_setting(module, ast_class, expected_type):
    """Helper to verify nodes visited by type inference visitor of astroid class has been properly transformed."""
    result = [n.type_constraints.type for n in module.nodes_of_class(ast_class)]
    assert [expected_type] == result


def _verify_node_value_typematch(module):
    """Helper to verify that AST node has the same type as it's value's"""
    for n in module.nodes_of_class(astroid.Expr):
        assert n.value.type_constraints.type == n.type_constraints.type


def _index_input_formatter(var_input, index):
    """Helper to format input for testing index type inference visitor."""
    return repr(var_input) + "[" + repr(index) + "]"


def _parse_dictionary_to_program(variables_dict):
    program = ""
    # parse dictionary into input program
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
        program += variable_name + " = " + repr(variables_dict[variable_name]) + "\n"
    return program
