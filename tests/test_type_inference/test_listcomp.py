import astroid
import nose
from hypothesis import settings, given
from typing import List
import tests.custom_hypothesis_support as cs
import hypothesis.strategies as hs
settings.load_profile("pyta")


@given(cs.homogeneous_iterable)
def test_list_comprehension_single_target_name_homogeneous_iterable(iterable):
    """Test Comprehension node visitor representing a comprehension expression with a single target and a
    name expression over a homogeneous list."""
    program = f'a = [num for num in {repr(iterable)}]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    if hasattr(listcomp_node.generators[0].iter.type_constraints.type, '__args__'):
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])
    else:
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


@given(cs.random_list(min_size=1))
def test_list_comprehension_single_target_name_heterogeneous_iterable(iterable):
    """Test Comprehension node visitor representing a comprehension expression with a single target and a
    name expression over a heterogeneous list."""
    program = f'a = [num for num in {repr(iterable)}]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    # test whether the target variables have been unified correctly
    # does the type of the elt, wrapped in a List form equal the type of concrete lookup of a
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    if hasattr(listcomp_node.generators[0].iter.type_constraints.type, '__args__'):
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])
    else:
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


@given(hs.lists(cs.homogeneous_list(min_size=1), min_size=1))
def test_list_comprehension_single_target_name_nested_homogeneous(iterable):
    """Test Comprehension node visitor representing a nested comprehension expression with a name expression and
    a single target over a homogeneous list."""
    program = f'a = [num for sublist in {repr(iterable)} for num in sublist]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    if hasattr(listcomp_node.generators[0].iter.type_constraints.type, '__args__'):
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])
    else:
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


@given(hs.lists(cs.random_list(min_size=1), min_size=1))
def test_list_comprehension_single_target_name_nested_heterogeneous(iterable):
    """Test Comprehension node visitor representing a nested comprehension expression with a name expression and
    a single target over a heterogeneous list."""
    program = f'a = [num for sublist in {repr(iterable)} for num in sublist]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    if hasattr(listcomp_node.generators[0].iter.type_constraints.type, '__args__'):
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])
    else:
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])



@given(hs.lists(cs.homogeneous_list(min_size=1), min_size=1))
def test_list_comprehension_multi_target_binop_nested_homogeneous(iterable):
    """test comprehension node visitor representing a nested comprehension expression with multiple targets and binary
    operations expressions performed on the targets over a homogeneous list."""
    program = f'a = [num1 + num2 for sublist in {repr(iterable)} for num1, num2 in sublist]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    if hasattr(listcomp_node.generators[0].iter.type_constraints.type, '__args__'):
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])
    else:
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


@given(hs.lists(cs.random_list(min_size=1), min_size=1))
def test_list_comprehension_multi_target_binop_nested_heterogeneous(iterable):
    """Test Comprehension node visitor representing a nested comprehension expression with multiple targets and binary
    operations expressions performed on the targets over a homogeneous list."""
    program = f'a = [num1 + num2 for sublist in {repr(iterable)} for num1, num2 in sublist]'
    module, TypeInferrer = cs._parse_text(program)
    listcomp_node = list(module.nodes_of_class(astroid.ListComp))[0]
    target_tvar = listcomp_node.type_environment.lookup_in_env(list(listcomp_node.locals.keys())[0])
    iter_type = listcomp_node.generators[0].iter.type_constraints.type
    assigned_tvar = module.type_environment.lookup_in_env('a')
    expected_type = TypeInferrer.type_constraints.lookup_concrete(listcomp_node.elt.type_constraints.type)
    if hasattr(listcomp_node.generators[0].iter.type_constraints.type, '__args__'):
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type.__args__[0]) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])
    else:
        assert (TypeInferrer.type_constraints.lookup_concrete(target_tvar) == iter_type) and \
               (TypeInferrer.type_constraints.lookup_concrete(assigned_tvar) == List[expected_type])


if __name__ == '__main__':
    nose.main()
