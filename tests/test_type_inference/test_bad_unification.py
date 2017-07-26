import astroid
import nose
from hypothesis import given, settings
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
from python_ta.typecheck.base import _node_to_type
settings.load_profile("pyta")


# def test_bad_unify_assigned_binop_builtins():
#     """Test whether unification algorithm is failing properly on trying to call a binary builtin operation
#      of the wrong type on a pre-assigned variable.
#     """
#     program = f'a = 5\n' \
#               f'a + "bob"\n'
#     module, inferer = cs._parse_text(program)
#     # TODO: does the type of the BinOp node correspond to correct TypeErrorInfo object?
#     boi = 1

def test_bad_unify_user_defined_annotated_call():
    """Test whether unification algorithm is failing as expected on trying to call an annotated user-defined function
    on the wrongly-typed arguments.
    """
    program = f'def add(num1: int, num2: int) -> int:\n' \
              f'    return num1 + num2\n' \
              f'\n' \
              f'add(1, "bob")\n'
    module, inferer = cs._parse_text(program)
    call_node = list(module.nodes_of_class(astroid.Call))[0]
    # TODO: fix expected error msg.
    expected_msg = f'U fukd up Boi'
    assert call_node.type_constraints.type.msg == expected_msg



if __name__ == '__main__':
    nose.main()
