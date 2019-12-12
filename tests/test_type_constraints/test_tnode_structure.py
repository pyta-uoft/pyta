from .. import custom_hypothesis_support as cs
import astroid
from typing import *
from typing import ForwardRef, _GenericAlias
import pytest
from python_ta.typecheck.base import TypeConstraints, _TNode, TypeFail
from sample_usage.draw_tnodes import gen_graph_from_nodes


def tc_to_disjoint(tc: TypeConstraints) -> List[Set[Union[type, str]]]:
    tnode_list = tc._nodes.copy()
    disjoint_set = []
    while tnode_list:
        cur_tnode = tnode_list[0]
        new_set = set()
        open_nodes = [cur_tnode]
        visited_nodes = []
        while open_nodes:
            cur_open_node = open_nodes[0]
            if isinstance(cur_open_node.type, TypeVar) or isinstance(cur_open_node.type, _GenericAlias):
                new_set.add(str(cur_open_node.type))
            else:
                new_set.add(cur_open_node.type)
            for e in cur_open_node.adj_list:
                if e[0] not in visited_nodes and e[0] not in open_nodes:
                    open_nodes.append(e[0])
            visited_nodes.append(cur_open_node)
            if cur_open_node in tnode_list:
                tnode_list.remove(cur_open_node)
            open_nodes.remove(cur_open_node)
        disjoint_set.append(new_set)
    return disjoint_set


def compare_list_sets(s1: List[Set[Union[type, str]]], s2: List[Set[Union[type, str]]]):
    list_sets_1 = [{str(t) for t in s} for s in s1]
    list_sets_2 = [{str(t) for t in s} for s in s2]
    assert len(list_sets_1) == len(list_sets_2)
    while list_sets_1:
        set1 = list_sets_1[0]
        found_set = None
        for set2 in list_sets_2:
            if set1 == set2:
                found_set = set2
        if found_set:
            list_sets_1.remove(set1)
            list_sets_2.remove(found_set)
        else:
            assert False
    assert True


def test_one_var():
    src = """
    a = 1
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{int, '~_TV0'}]
    compare_list_sets(actual_set, expected_set)


def test_typefail():
    src = """
    a = 1
    b = "hello"
    a = b
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{int, '~_TV0'}, {str, '~_TV1'}]
    compare_list_sets(actual_set, expected_set)


def test_multi_var_int():
    src = """
    a = 1
    b = 2
    c = 3
    d = 4
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{int, '~_TV0', '~_TV1', '~_TV2', '~_TV3'}]
    compare_list_sets(actual_set, expected_set)


def test_multi_var():
    src = """
    a = 1
    b = "Hello"
    c = False
    d = 4.0
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{int, '~_TV0'}, {'~_TV1', str}, {'~_TV2', bool}, {'~_TV3', float}]
    compare_list_sets(actual_set, expected_set)


def test_var_chain():
    src = """
    a = 1
    b = a
    c = b
    d = c
    e = d
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{int, '~_TV0', '~_TV1', '~_TV2', '~_TV3', '~_TV4'}]
    compare_list_sets(actual_set, expected_set)


def test_list_int():
    src = """
    l = [1,2,3]
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_TV0', 'typing.List[int]'}, {int}]
    compare_list_sets(actual_set, expected_set)


def test_any_list():
    src = """
    l = [1, "string", False]
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_TV0', 'typing.List[typing.Any]'}, {int}, {str}]
    compare_list_sets(actual_set, expected_set)


def test_tuple_int():
    src = """
    l = (1, 2)
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_TV0', 'typing.Tuple[int, int]'}]
    compare_list_sets(actual_set, expected_set)


def test_tuple_int_str():
    src = """
    l = (1, "Hello")
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_TV0', 'typing.Tuple[int, str]'}]
    compare_list_sets(actual_set, expected_set)


def test_elt():
    src = """
    l = [1,2,3]
    e = l[0]
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_TV0', 'typing.List[~_TV2]', 'typing.List[int]'}, {'~_TV1', int, '~_TV2'}]
    compare_list_sets(actual_set, expected_set)


tc = TypeConstraints()


def test_forward_ref(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    assert isinstance(tc.unify(ForwardRef('A'), ForwardRef('B')), TypeFail)
    assert tc.unify(ForwardRef('A'), ForwardRef('A')).getValue() == ForwardRef('A')
    assert tc.unify(t0, ForwardRef('A')).getValue() == ForwardRef('A')
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0', ForwardRef('A')}, {ForwardRef('B')}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_polymorphic_callable(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    t1 = tc.fresh_tvar()
    t2 = tc.fresh_tvar()
    tc.unify(t1, Callable[[int], int])
    tc.unify(t2, Callable[[t0], t0])
    tc.unify(t1, t2)
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0', int},
                    {'~_TV1', '~_TV2', 'typing.Callable[[int], int]',
                     'typing.Callable[[~_TV0], ~_TV0]'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_polymorphic_callable2(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    t1 = tc.fresh_tvar()
    t2 = tc.fresh_tvar()
    tc.unify(t1, Callable[[t0], int])
    tc.unify(t2, Callable[[int], t0])
    tc.unify(t1, t2)
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0', int},
                    {'~_TV1', '~_TV2', 'typing.Callable[[~_TV0], int]',
                     'typing.Callable[[int], ~_TV0]'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_polymorphic_callable3(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    t1 = tc.fresh_tvar()
    t2 = tc.fresh_tvar()
    tc.unify(t1, Callable[[t0], t0])
    tc.unify(t2, t1)
    tc.unify(t2, Callable[[int], int])
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0', int},
                    {'~_TV1', '~_TV2', 'typing.Callable[[int], int]',
                     'typing.Callable[[~_TV0], ~_TV0]'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_polymorphic_callable4(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    t1 = tc.fresh_tvar()
    t2 = tc.fresh_tvar()
    tc.unify(t1, Callable[[t0], t0])
    tc.unify(t2, t1)
    assert isinstance(tc.unify(t2, Callable[[int], str]), TypeFail)
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0', int},
                    {'~_TV1', '~_TV2', 'typing.Callable[[~_TV0], ~_TV0]'},
                    {'typing.Callable[[int], str]'}, {str}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_polymorphic_callable5(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    tc.unify(Callable[[Callable[[int, t0], int], int], t0],
             Callable[[Callable[[int, int], int], int], t0])
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0', int},
                    {'typing.Callable[[int, ~_TV0], int]', 'typing.Callable[[int, int], int]'},
                    {'typing.Callable[[typing.Callable[[int, ~_TV0], int], int], ~_TV0]',
                     'typing.Callable[[typing.Callable[[int, int], int], int], ~_TV0]'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_can_unify_callable(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    assert not tc.can_unify(Callable[[t0, t0], int], Callable[[str, int], int])
    # make sure tc is unchanged
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_TV0'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


# Inheritance

def test_userdefn_inheritance_simple(draw=False):
    src = """
    class A:
        pass

    class B:
        pass

    class C(A, B):
        pass

    a = A()
    b = B()
    c = C()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tc = ti.type_constraints
    a, b, c = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)]

    assert isinstance(tc.unify(a, b), TypeFail)
    assert tc.unify(c, a).getValue() == ForwardRef('C')
    assert isinstance(tc.unify(a, c), TypeFail)  # note that order matters!
    assert tc.unify(c, b).getValue() == ForwardRef('C')
    assert isinstance(tc.unify(b, c), TypeFail)

    actual_set = tc_to_disjoint(tc)
    expected_set = [
        {'~_TV0', Type[ForwardRef('A')]},
        {'~_TV1', Type[ForwardRef('B')]},
        {'~_TV2', Type[ForwardRef('C')]},
        {'~_TV3', ForwardRef('A')},
        {'~_TV4', ForwardRef('B')},
        {'~_TV5', ForwardRef('C')}
    ]

    # _TNodes should be unchanged after unification
    compare_list_sets(actual_set, expected_set)

    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_userdefn_inheritance_multilevel(draw=False):
    src = """
    class A:
        pass

    class B(A):
        pass

    class C(B):
        pass

    a = A()
    b = B()
    c = C()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tc = ti.type_constraints
    a, b, c = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)]

    assert tc.unify(b, a).getValue() == ForwardRef('B')
    assert tc.unify(c, b).getValue() == ForwardRef('C')
    assert tc.unify(c, a).getValue() == ForwardRef('C')
    assert isinstance(ti.type_constraints.unify(b, c), TypeFail)

    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_builtin_abst_inheritance(draw=False):
    src = """
    x = 3
    # float takes in an argument of type SupportsFloat
    y = float(x)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    tc = ti.type_constraints
    actual_set = tc_to_disjoint(tc)
    assert {'~_TV0', int} in actual_set
    assert {'~_TV1', float} in actual_set
    if draw:
        gen_graph_from_nodes(tc._nodes)


# TODO: more tests for builtin inheritance


# Inheritance-based method lookup

def test_userdefn_mro_simple(draw=False):
    src = """
    class A:
        def foo(self):
            return 0
            
    class B(A):
        pass
        
    b = B()
    x = b.foo()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    _, b, x = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(x).getValue() == int
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_userdefn_mro_multilevel(draw=False):
    src = """
    class A:
        def foo(self):
            return 0
            
    class B:
        pass
        
    class C(A):
        pass
        
    class D(B, C):
        pass
        
    d = D()
    x = d.foo()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    _, d, x = [ti.lookup_typevar(node, node.name) for node
               in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(x).getValue() == int
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_userdefn_mro_diamond(draw=False):
    src = """
    class A:
        pass
            
    class B(A):
        def foo(self):
            return 'a'
        
    class C(A):
        def foo(self):
            return 0
        
    class D(B,C):
        pass
        
    d = D()
    x = d.foo() # this is a call to B.foo()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    _, _, d, x = [ti.lookup_typevar(node, node.name) for node
                  in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(x).getValue() == str
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


@pytest.mark.skip(reason='Cannot yet handle Generic Protocols (SupportsAbs[T])')
def test_builtin_abst_base_mro(draw=False):
    src = """
    x = 3 # x descends from SupportsAbs[int]
    y = abs(x)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x, y = [ti.lookup_typevar(node, node.name) for node
            in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(y).getValue() == int
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_builtin_call_simple_mro(draw=False):
    src = """
    class A:
        pass
        
    a = A()
    x = repr(a)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    a, x = [ti.lookup_typevar(node, node.name) for node
            in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(x).getValue() == str
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_builtin_binop_inheritance(draw=False):
    src = """
    x = 1.0 + 3
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == float
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_builtin_comp_inheritance(draw=False):
    src = """
    x = (3 == 'abc')
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == bool
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_userdefn_inherits_from_builtin(draw=False):
    src = """
    class MyStr(str):
        pass
        
    s = MyStr()
    x = s.lower()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    s, x = [ti.lookup_typevar(node, node.name) for node
            in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(x).getValue() == str
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_userdefn_overrides_builtin(draw=False):
    src = """
    class MyStr(str):
        def lower(self):
            return 0

    s = MyStr()
    x = s.lower()
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    _, s, x = [ti.lookup_typevar(node, node.name) for node
            in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(x).getValue() == int
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_builtin_generic_inheritance_init(draw=False):
    src = """
    x = set([1,2,3])
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x = [ti.lookup_typevar(node, node.name) for node
         in ast_mod.nodes_of_class(astroid.AssignName)][0]
    assert ti.type_constraints.resolve(x).getValue() == Set[int]


def test_builtin_generic_inheritance_method_lookup(draw=False):
    src = """
    x = set([1,2,3])
    y = x.symmetric_difference([2,3])
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x, y = [ti.lookup_typevar(node, node.name) for node
            in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(y).getValue() == Set[int]
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)


def test_builtin_generic_inheritance_overloaded_init(draw=False):
    src = """
    x = set([1,2,3])
    y = list(x)
    """
    ast_mod, ti = cs._parse_text(src, reset=True)
    x, y = [ti.lookup_typevar(node, node.name) for node
            in ast_mod.nodes_of_class(astroid.AssignName)]
    assert ti.type_constraints.resolve(y).getValue() == List[int]
    if draw:
        gen_graph_from_nodes(ti.type_constraints._nodes)
