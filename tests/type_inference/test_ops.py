import nose
from hypothesis import given, settings
import tests.custom_hypothesis_support as cs
from python_ta.transforms.type_inference_visitor import *
settings.load_profile("pyta")


@given(cs.non_bool_primitive_values, cs.boolean_operator(), cs.non_bool_primitive_values)
def test_binop_non_bool_uniform_concrete(left_operand, operator, right_operand):
    """Test type setting of BinOp node(s) with non-boolean operands."""
    program = f'{repr(left_operand)} {operator} {repr(right_operand)}\n'
    module = cs._parse_text(program)
    binop_node = list(module.nodes_of_class(astroid.BinOp))[0]
    try:
        exp_func_type = TYPE_STORE.lookup_function(op_to_dunder(operator), type(left_operand), type(right_operand))
        exp_return_type = exp_func_type.__args__[-1]
        assert binop_node.type_constraints.type == exp_return_type
    except KeyError:
        assert True

if __name__ == '__main__':
    nose.main()
