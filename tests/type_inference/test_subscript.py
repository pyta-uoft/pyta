import astroid
import nose
from hypothesis import given, settings
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.homogeneous_list(min_size=1), hs.integers())
def test_inference_list_subscript(input_list, index):
    """Test whether visitor properly set the type constraint of Subscript node representing list-index access."""
    program = f'{input_list}[{index}]'
    module = cs._parse_text(program)
    subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
    assert subscript_node.type_constraints.type == type(input_list[0])


@given(cs.random_dict_variable_value(min_size=1))
def test_inference_dict_subscript(input_dict):
    for index in input_dict:
        program = f'{input_dict}[{index}]'
        module = cs._parse_text(program)
        subscript_node = list(module.nodes_of_class(astroid.Subscript))[0]
        assert subscript_node.type_constraints.type == type(input_dict[index])


if __name__ == '__main__':
    nose.main()
