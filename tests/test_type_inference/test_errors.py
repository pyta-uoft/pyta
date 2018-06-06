import astroid
import nose
from hypothesis import settings
from unittest import SkipTest
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


def test_incompatible_binop_call():
    """ User tries to call a builtin binary operation on arguments of the wrong type.
    """
    program = f'5 + "string"\n'
    try:
        module, inferer = cs._parse_text(program)
    except:
        raise SkipTest()
    binop_node = next(module.nodes_of_class(astroid.BinOp))
    expected_msg = "You cannot add an int, 5, and a str, 'string'. " \
                   "Perhaps you wanted to cast the integer into a string or vice versa?"
    assert binop_node.inf_type.getValue() == expected_msg


def test_incompatible_unaryop_call():
    """User tries to call a builtin unary operation on an argument of the wrong type.
    """
    program = f'~["D"]'
    try:
        module, inferer = cs._parse_text(program)
    except:
        raise SkipTest()
    unaryop_node = next(module.nodes_of_class(astroid.UnaryOp))
    expected_msg = "You cannot take the bitwise inverse of a List, ['D']."
    assert unaryop_node.inf_type.getValue() == expected_msg


def test_incompatible_subscript_list():
    """User tries to access an element of a list using the wrong type of index.
    """
    program = f'[1,2,3]["one"]'
    try:
        # TODO: Don't need inferer?
        module, inferer = cs._parse_text(program)
    except:
        raise SkipTest()
    subscript_node = next(module.nodes_of_class(astroid.Subscript))
    expected_msg = "You can only access elements of a list using an int. You used a str, 'one'."
    assert(subscript_node.inf_type.getValue() == expected_msg)


if __name__ == '__main__':
    nose.main()
