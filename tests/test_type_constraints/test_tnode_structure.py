import tests.custom_hypothesis_support as cs
from nose import SkipTest
from typing import *
from typing import _ForwardRef
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
            if isinstance(cur_open_node.type, TypeVar) or isinstance(cur_open_node.type, GenericMeta):
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
    expected_set = [{int, '~_T0'}]
    compare_list_sets(actual_set, expected_set)


def test_typefail():
    src = """
    a = 1
    b = "hello"
    a = b
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{int, '~_T0'}, {str, '~_T1'}]
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
    expected_set = [{int, '~_T0', '~_T1', '~_T2', '~_T3'}]
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
    expected_set = [{int, '~_T0'}, {'~_T1', str}, {'~_T2', bool}, {'~_T3', float}]
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
    expected_set = [{int, '~_T0', '~_T1', '~_T2', '~_T3', '~_T4'}]
    compare_list_sets(actual_set, expected_set)


def test_list_int():
    src = """
    l = [1,2,3]
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_T0', 'typing.List[int]'}, {int}]
    compare_list_sets(actual_set, expected_set)


def test_any_list():
    src = """
    l = [1, "string", False]
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_T0', 'typing.List[typing.Any]'}, {int}, {str}]
    compare_list_sets(actual_set, expected_set)


def test_tuple_int():
    src = """
    l = (1, 2)
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_T0', 'typing.Tuple[int, int]'}]
    compare_list_sets(actual_set, expected_set)


def test_tuple_int_str():
    src = """
    l = (1, "Hello")
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_T0', 'typing.Tuple[int, str]'}]
    compare_list_sets(actual_set, expected_set)


def test_elt():
    src = """
    l = [1,2,3]
    e = l[0]
    """
    ast_mod, ti = cs._parse_text(src)
    actual_set = tc_to_disjoint(ti.type_constraints)
    expected_set = [{'~_T0', 'typing.List[~_T2]', 'typing.List[int]'}, {'~_T1', int, '~_T2'}]
    compare_list_sets(actual_set, expected_set)


tc = TypeConstraints()


def test_forward_ref(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    assert isinstance(tc.unify(_ForwardRef('A'), _ForwardRef('B')), TypeFail)
    assert tc.unify(_ForwardRef('A'), _ForwardRef('A')).getValue() == _ForwardRef('A')
    assert tc.unify(t0, _ForwardRef('A')).getValue() == _ForwardRef('A')
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_T0', _ForwardRef('A')}, {_ForwardRef('B')}]
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
    expected_set = [{'~_T0', int},
                    {'~_T1', '~_T2', 'typing.Callable[[int], int]',
                     'typing.Callable[[~_T0], ~_T0]'}]
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
    expected_set = [{'~_T0', int},
                    {'~_T1', '~_T2', 'typing.Callable[[~_T0], int]',
                     'typing.Callable[[int], ~_T0]'}]
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
    expected_set = [{'~_T0', int},
                    {'~_T1', '~_T2', 'typing.Callable[[int], int]',
                     'typing.Callable[[~_T0], ~_T0]'}]
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
    expected_set = [{'~_T0', int},
                    {'~_T1', '~_T2', 'typing.Callable[[~_T0], ~_T0]',
                     'typing.Callable[[int], str]'}, {str}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_polymorphic_callable5(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    tc.unify(Callable[[Callable[[int, t0], int], int], t0],
             Callable[[Callable[[int, int], int], int], t0])
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_T0', int},
                    {'typing.Callable[[int, ~_T0], int]', 'typing.Callable[[int, int], int]'},
                    {'typing.Callable[[typing.Callable[[int, ~_T0], int], int], ~_T0]',
                     'typing.Callable[[typing.Callable[[int, int], int], int], ~_T0]'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)


def test_can_unify_callable(draw=False):
    tc.reset()
    t0 = tc.fresh_tvar()
    assert not tc.can_unify(Callable[[t0, t0], int], Callable[[str, int], int])
    # make sure tc is unchanged
    actual_set = tc_to_disjoint(tc)
    expected_set = [{'~_T0'}]
    compare_list_sets(actual_set, expected_set)
    if draw:
        gen_graph_from_nodes(tc._nodes)
