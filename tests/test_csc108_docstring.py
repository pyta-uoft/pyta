from typing import *
from docstring.csc108_docstring import *


def test_missing_all():
    parsed = ParsedDocstring108("""""")
    assert not parsed.signature_args_list
    assert not parsed.signature_return_type
    assert not parsed.description
    assert not parsed.doctests


def test_missing_signature():
    parsed = ParsedDocstring108("""Description\n>>> myFunc()\nNone""")
    assert not parsed.signature_args_list
    assert not parsed.signature_return_type
    assert parsed.description == 'Description'
    assert parsed.doctests == '>>> myFunc()\nNone'


def test_missing_description():
    parsed = ParsedDocstring108("""(int) -> bool\n>>> f(5)\n'Yes'""")
    assert len(parsed.signature_args_list) == 1
    assert parsed.signature_args_list[0] == int
    assert parsed.signature_return_type == bool
    assert not parsed.description
    assert parsed.doctests == ">>> f(5)\n'Yes'"


def test_missing_doctests():
    parsed = ParsedDocstring108("""(int) -> bool\nDescription\nHere""")
    assert len(parsed.signature_args_list) == 1
    assert parsed.signature_args_list[0] == int
    assert parsed.signature_return_type == bool
    assert parsed.description == 'Description\nHere'
    assert not parsed.doctests


def test_simple_docstring():
    parsed = ParsedDocstring108("""(int) -> bool
    Description
    >>> f(5)
    'Yes'""")
    assert len(parsed.signature_args_list) == 1
    assert parsed.signature_args_list[0] == int
    assert parsed.signature_return_type == bool
    assert parsed.description == 'Description'
    assert parsed.doctests == ">>> f(5)\n'Yes'"


def test_advanced_docstring():
    parsed = ParsedDocstring108("""(list of int, set of set of bool, tuple of (str, int), dict of {obj, NoneType}) -> list of list of list of CustomClass
    Description
    >>> f(5)
    'Yes'""")
    assert len(parsed.signature_args_list) == 4
    assert parsed.signature_args_list[0] == List[int]
    assert parsed.signature_args_list[1] == Set[Set[bool]]
    assert parsed.signature_args_list[2] == Tuple[str, int]
    assert parsed.signature_args_list[3] == Dict[Any, type(None)]
    assert parsed.signature_return_type == List[List[List['CustomClass']]]
    assert parsed.description == 'Description'
    assert parsed.doctests == ">>> f(5)\n'Yes'"


def test_valid_empty_docstring():
    parsed = ParsedDocstring108("""() -> bool""")
    assert len(parsed.signature_args_list) == 0
    assert parsed.signature_return_type == bool


def test_description_with_right_arrows():
    parsed = ParsedDocstring108("""(int) -> bool\nTest > arrows >> Test""")
    assert len(parsed.signature_args_list) == 1
    assert parsed.signature_args_list[0] == int
    assert parsed.signature_return_type == bool
    assert parsed.description == 'Test > arrows >> Test'
    assert not parsed.doctests


def test_malformed_substring():
    try:
        ParsedDocstring108("""(int) -> -> bool""")
        assert False
    except:
        pass


def test_malformed_docstring_list():
    try:
        ParsedDocstring108("""(list of) -> -> bool""")
        assert False
    except:
        pass


def test_malformed_docstring_list_nested():
    try:
        ParsedDocstring108("""(list of set int) -> -> bool""")
        assert False
    except:
        pass


def test_malformed_docstring_tuple():
    try:
        ParsedDocstring108("""(tuple of (int, )) -> -> bool""")
        assert False
    except:
        pass
