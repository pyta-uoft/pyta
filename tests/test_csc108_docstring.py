from typing import *

from python_ta.docstring.csc108_docstring import *


def test_simple_docstring():
    parsed_docstring = parse_csc108_docstring('(int) -> bool')
    assert len(parsed_docstring) == 4
    assert parsed_docstring[0] == [int]
    assert parsed_docstring[1] == bool


def test_collection_simple_docstring():
    parsed_docstring = parse_csc108_docstring('(list of list of int) -> dict of {int, bool}')
    assert len(parsed_docstring) == 4
    assert parsed_docstring[0] == [List[List[int]]]
    assert parsed_docstring[1] == Dict[int, bool]


def test_simple_docstring_with_spaces():
    parsed_docstring = parse_csc108_docstring('  (int)  ->    bool ')
    assert len(parsed_docstring) == 4
    assert parsed_docstring[0] == [int]
    assert parsed_docstring[1] == bool


def test_collection_all_docstring():
    parsed_docstring = parse_csc108_docstring('(list of tuple of (int, bool), set of RandomClass) -> NoneType')
    assert len(parsed_docstring) == 4
    assert parsed_docstring[0][0] == List[Tuple[int, bool]]
    # Comparing with forwardref's fails for some unknown reason (needs investigating).
    desired_type = Set[typing._ForwardRef('RandomClass')]
    assert str(desired_type) == str(parsed_docstring[0][1])
    assert parsed_docstring[1] == None.__class__


def test_tuple_single_element():
    parsed_docstring = parse_csc108_docstring('(tuple of (int)) -> int')
    print(parsed_docstring)
    assert len(parsed_docstring) == 4
    desired_type = Tuple[int]
    assert str(desired_type) == str(parsed_docstring[0][0])
    assert parsed_docstring[1] == int


def test_empty_docstring():
    parsed_docstring = parse_csc108_docstring('() -> int')
    print(parsed_docstring)
    assert len(parsed_docstring) == 4
    assert parsed_docstring[1] == int


def test_malformed_substring():
    try:
        parse_csc108_docstring("""(int) -> -> bool""")
        assert False
    except:
        pass


def test_malformed_docstring_list():
    try:
        parse_csc108_docstring("""(list of) -> -> bool""")
        assert False
    except:
        pass


def test_malformed_docstring_list_nested():
    try:
        parse_csc108_docstring("""(list of set int) -> -> bool""")
        assert False
    except:
        pass


def test_malformed_docstring_tuple():
    try:
        parse_csc108_docstring("""(tuple of (int, )) -> -> bool""")
        assert False
    except:
        pass


# def test_missing_all():
#     parsed = ParsedDocstring108("""""")
#     assert not parsed.signature_args_list
#     assert not parsed.signature_return_type
#     assert not parsed.description
#     assert not parsed.doctests
#
#
# def test_missing_signature():
#     parsed = ParsedDocstring108("""Description\n>>> myFunc()\nNone""")
#     assert not parsed.signature_args_list
#     assert not parsed.signature_return_type
#     assert parsed.description == 'Description'
#     assert parsed.doctests == '>>> myFunc()\nNone'
#
#
# def test_missing_description():
#     parsed = ParsedDocstring108("""(int) -> bool\n>>> f(5)\n'Yes'""")
#     assert len(parsed.signature_args_list) == 1
#     assert parsed.signature_args_list[0] == int
#     assert parsed.signature_return_type == bool
#     assert not parsed.description
#     assert parsed.doctests == ">>> f(5)\n'Yes'"
#
#
# def test_missing_doctests():
#     parsed = ParsedDocstring108("""(int) -> bool\nDescription\nHere""")
#     assert len(parsed.signature_args_list) == 1
#     assert parsed.signature_args_list[0] == int
#     assert parsed.signature_return_type == bool
#     assert parsed.description == 'Description\nHere'
#     assert not parsed.doctests
#
#
# def test_simple_docstring():
#     parsed = ParsedDocstring108("""(int) -> bool
#     Description
#     >>> f(5)
#     'Yes'""")
#     assert len(parsed.signature_args_list) == 1
#     assert parsed.signature_args_list[0] == int
#     assert parsed.signature_return_type == bool
#     assert parsed.description == 'Description'
#     assert parsed.doctests == ">>> f(5)\n'Yes'"
#
#
# def test_advanced_docstring():
#     parsed = ParsedDocstring108("""(list of int, set of set of bool, tuple of (str, int), dict of {obj, NoneType}) -> list of list of list of CustomClass
#     Description
#     >>> f(5)
#     'Yes'""")
#     assert len(parsed.signature_args_list) == 4
#     assert parsed.signature_args_list[0] == List[int]
#     assert parsed.signature_args_list[1] == Set[Set[bool]]
#     assert parsed.signature_args_list[2] == Tuple[str, int]
#     assert parsed.signature_args_list[3] == Dict[Any, type(None)]
#     assert parsed.signature_return_type == List[List[List['CustomClass']]]
#     assert parsed.description == 'Description'
#     assert parsed.doctests == ">>> f(5)\n'Yes'"
#
#
# def test_valid_empty_docstring():
#     parsed = ParsedDocstring108("""() -> bool""")
#     assert len(parsed.signature_args_list) == 0
#     assert parsed.signature_return_type == bool
#
#
# def test_description_with_right_arrows():
#     parsed = ParsedDocstring108("""(int) -> bool\nTest > arrows >> Test""")
#     assert len(parsed.signature_args_list) == 1
#     assert parsed.signature_args_list[0] == int
#     assert parsed.signature_return_type == bool
#     assert parsed.description == 'Test > arrows >> Test'
#     assert not parsed.doctests
