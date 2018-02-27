import astroid
import nose
from hypothesis import given, settings, assume, HealthCheck
import tests.custom_hypothesis_support as cs
from python_ta.transforms.type_inference_visitor import OP_TO_DUNDER_BINARY
settings.load_profile("pyta")


@given(cs.binop_node())
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_binop_non_bool_concrete(node):
    """Test type setting of BinOp node(s) with non-boolean operands."""
    module, inferer = cs._parse_text(node)
    binop_node = list(module.nodes_of_class(astroid.BinOp))[0]
    left_type, right_type = binop_node.left.type_constraints.type, binop_node.right.type_constraints.type
    try:
        exp_func_type = inferer.type_store.lookup_function(OP_TO_DUNDER_BINARY[node.op], left_type, right_type)
        exp_return_type = exp_func_type.__args__[-1]
    except KeyError:
        exp_return_type = None
    assume(exp_return_type is not None)
    assert binop_node.type_constraints.type == exp_return_type


if __name__ == '__main__':
    nose.main()
