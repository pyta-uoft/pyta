import astroid
import nose
from hypothesis import given, settings
import tests.custom_hypothesis_support as cs
from python_ta.typecheck.type_store import TYPE_STORE
settings.load_profile("pyta")


@given(cs.non_bool_primitive_values, cs.boolean_operator(), cs.non_bool_primitive_values)
def test_binop_non_bool_concrete(left_operand, operator, right_operand):
    """Test type setting of BinOp node(s) with non-boolean operands."""
    program = f'{left_operand} {operator} {right_operand}\n'
    module = cs._parse_text(program)
    binop_node = list(module.nodes_of_class(astroid.BinOp))[0]
    expected_func_type = TYPE_STORE.lookup_function(operator, type(left_operand), type(right_operand))
    expected_return_type = expected_func_type.__args__[-1]
    assert binop_node.type_constraints.type == expected_return_type


if __name__ == '__main__':
    nose.main()