import astroid
import nose
from hypothesis import settings
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


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
    expected_msg = 'Bad unify_call of function typing.Callable[[int, int], int] given args: int, str'
    assert call_node.type_constraints.type.msg == expected_msg



if __name__ == '__main__':
    nose.main()
