import astroid

from hypothesis import settings
from .. import custom_hypothesis_support as cs

from pytest import skip
settings.load_profile("pyta")


def test_incompatible_binop_call():
    """User tries to call a builtin binary operation on arguments of the wrong type.
    """
    skip('SKIP FOR NOW.')
    program = f'5 + "string"\n'
    module, _ = cs._parse_text(program)
    binop_node = next(module.nodes_of_class(astroid.BinOp))
    expected_msg = "You cannot add an int, 5, and a str, 'string'. " \
                   "Perhaps you wanted to cast the integer into a string or vice versa?"
    assert binop_node.inf_type.getValue() == expected_msg


def test_incompatible_unaryop_call():
    """User tries to call a builtin unary operation on an argument of the wrong type.
    """
    skip('SKIP FOR NOW.')
    program = f'~["D"]'
    module, _ = cs._parse_text(program)
    unaryop_node = next(module.nodes_of_class(astroid.UnaryOp))
    expected_msg = "You cannot take the bitwise inverse of a list of str, ['D']."
    assert unaryop_node.inf_type.getValue() == expected_msg


def test_incompatible_subscript_list():
    """User tries to access an element of a list using the wrong type of index.
    """
    skip('SKIP FOR NOW.')
    program = f'[1,2,3]["one"]'
    module, _ = cs._parse_text(program)
    subscript_node = next(module.nodes_of_class(astroid.Subscript))
    expected_msg = "You can only access elements of a list using an int. You used a str, 'one'."
    assert subscript_node.inf_type.getValue() == expected_msg


def test_incompatible_subscript_tuple():
    """User tries to access an element of a tuple using the wrong type of index.
    """
    skip('SKIP FOR NOW.')
    program = f'(1,2,3)["one"]'
    module, _ = cs._parse_text(program)
    subscript_node = next(module.nodes_of_class(astroid.Subscript))
    expected_msg = "You can only access elements of a tuple using an int. You used a str, 'one'."
    assert subscript_node.inf_type.getValue() == expected_msg


def test_incompatible_subscript_dictionary():
    """User tries to access an element of a dictionary using the wrong type of key.
    """
    skip('SKIP FOR NOW.')
    program = '''{ "1" : 1, "2" : 2, "3" : 3 }[1]'''
    module, _ = cs._parse_text(program)
    subscript_node = next(module.nodes_of_class(astroid.Subscript))
    expected_msg = "You tried to access an element of this dictionary using an int, 1, but the keys are of type str."
    assert subscript_node.inf_type.getValue() == expected_msg
