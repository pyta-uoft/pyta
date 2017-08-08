import astroid
import nose
from hypothesis import settings
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


def test_bad_attribute_access():
    """ User tries to access a non-existing attribute; or misspells the attribute name.
    """
    program = f'x = 1\n' \
              f'x.wrong_name\n'
    module, inferer = cs._parse_text(program)
    call_node = next(module.nodes_of_class(astroid.Call))
    expected_msg = "Attribute access error!\
    				In the Attribute node in line (2):\
    					the object "x" does not have the attribute "wrong_name"."
    assert call_node.type_constraints.type.msg == expected_msg


if __name__ == '__main__':
    nose.main()
