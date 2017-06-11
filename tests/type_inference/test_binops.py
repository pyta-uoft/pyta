import astroid
import nose
from hypothesis import given, settings, assume
import tests.custom_hypothesis_support as cs
from python_ta.transforms.type_inference_visitor import op_to_dunder_binary
settings.load_profile("pyta")


@given(cs.primitive_values, cs.non_boolean_operator, cs.primitive_values)
def test_binop_non_bool_concrete(left_operand, operator, right_operand):
    """Test type setting of BinOp node(s) with non-boolean operands."""
    program = f'{repr(left_operand)} {operator} {repr(right_operand)}\n'
    module, inferer = cs._parse_text(program)
    try:
        exp_func_type = inferer.type_store.lookup_function(op_to_dunder_binary(operator), type(left_operand), type(right_operand))
        exp_return_type = exp_func_type.__args__[-1]
    except KeyError:
        exp_return_type = None
    assume(exp_return_type is not None)
    binop_node = list(module.nodes_of_class(astroid.BinOp))[0]
    assert binop_node.type_constraints.type == exp_return_type


if __name__ == '__main__':
    nose.main()
