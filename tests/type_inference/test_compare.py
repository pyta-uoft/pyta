import astroid
import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.comparator_operator, hs.integers(), hs.integers())
def test_inference_list_subscript(operator, left_value, right_value):
    """Test type settting of  Compare node representing comparison between homogeneous-typed values."""
    #TODO: __eq__ has type Callable[[int, object], bool] and int does not unify with object.
    assume(operator != '==' and operator != '>=' and operator != '<=' and operator != '!=')
    program = f'{repr(left_value)} {operator} {repr(right_value)}'
    module, _ = cs._parse_text(program)
    compare_node = list(module.nodes_of_class(astroid.Compare))[0]
    assert compare_node.type_constraints.type == bool


if __name__ == '__main__':
    nose.main()
