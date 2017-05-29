import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
from python_ta.transforms.type_inference_visitor import *
settings.load_profile("pyta")


@given(cs.non_bool_primitive_values, cs.non_boolean_operator(), cs.non_bool_primitive_values)
def test_binop_non_bool_concrete(left_operand, operator, right_operand):
    """Test type setting of BinOp node(s) with non-boolean operands."""
    try:
        exp_func_type = TYPE_STORE.lookup_function(op_to_dunder(operator), type(left_operand), type(right_operand))
        exp_return_type = exp_func_type.__args__[-1]
    except KeyError:
        exp_return_type = None
    assume(exp_return_type is not None)
    program = f'{repr(left_operand)} {operator} {repr(right_operand)}\n'
    module = cs._parse_text(program)
    binop_node = list(module.nodes_of_class(astroid.BinOp))[0]
    assert binop_node.type_constraints.type == exp_return_type


if __name__ == '__main__':
    nose.main()
