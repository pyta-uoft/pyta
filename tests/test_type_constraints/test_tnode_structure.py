import tests.custom_hypothesis_support as cs
from typing import *
from python_ta.typecheck.base import TypeConstraints, _TNode


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
    list_sets_1 = s1.copy()
    list_sets_2 = s2.copy()
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
