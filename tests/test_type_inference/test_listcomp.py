import astroid
import nose
from hypothesis import settings
from typing import List
import tests.custom_hypothesis_support as cs
settings.load_profile("pyta")


def test_list_comprehension_single_target_name():
    """Test Comprehension node visitor representing a comprehension expression with a single target and a
    name expression."""
    program = f'a = [num for num in [1,2,3]]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    # test whether the target variables have been unified correctly
    # does the type of the elt, wrapped in a List form equal the type of concrete lookup of a
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
           (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


def test_list_comprehension_single_target_name_nested():
    """Test Comprehension node visitor representing a nested comprehension expression with a name expression and
    a single target."""
    program = f'a = [num for sublist in [[1, 2], [3,4]] for num in sublist]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
           (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


def test_list_comprehension_multi_target_binop_nested():
    """Test Comprehension node visitor representing a nested comprehension expression with multiple targets and binary
    operations expressions performed on the targets."""
    program = f'a = [num1 + num2 for sublist in [[1,2], [3,4]] for num1, num2 in sublist]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
           (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


if __name__ == '__main__':
    nose.main()
