"""Test suite for testing the InvalidNameChecker."""

import os
import re
import sys
import unittest

import astroid
import pylint.testutils
from astroid import nodes

import python_ta
from python_ta.checkers.invalid_name_checker import (
    InvalidNameChecker,
    _to_pascal_case,
    _to_snake_case,
    _to_upper_case_with_underscores,
)


class TestInvalidNameChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidNameChecker
    CONFIG = {
        "ignore_names": re.compile("(ignored[a-zA-Z0-9_]*)$"),
        "ignore_module_names": re.compile("(ignored_[a-zA-Z0-9_]*)$"),
        "constant_max_name_length": 20,
        "argument_max_name_length": 40,
        "class_attribute_max_name_length": 40,
        "type_alias_max_name_length": 15,
    }

    def set_up(self) -> None:
        """Perform the set up before each test case executes."""
        self.setup_method()

    def test_module_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid module name."""
        src = """
        i = "hi"
        """
        mod = astroid.parse(src)
        module_node, *_ = mod.nodes_of_class(nodes.Module)
        module_node.name = "l"
        msg = (
            f'"{module_node.name}" is a name that should be avoided. Change to something less '
            f"ambiguous and/or more descriptive."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="module-name-violation", node=module_node, args=msg, line=1
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(module_node)

    def test_module_name_underscore(self) -> None:
        """Test that the checker does not report an error when the module name starts with an
        underscore.
        """
        src = """
        i = "hi"
        """
        mod = astroid.parse(src)
        module_node, *_ = mod.nodes_of_class(nodes.Module)
        module_node.name = "_my_module"

        with self.assertNoMessages():
            self.checker.visit_module(module_node)

    def test_const_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid const name."""
        src = """
        const_not_upper = "it is not"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Constant name "{name}" should be in UPPER_CASE_WITH_UNDERSCORES format. '
            f'Suggested fix: "CONST_NOT_UPPER". '
            f"Constants should be all-uppercase words with each word separated by an underscore. A "
            f"single leading underscore can be used to denote a private constant."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_const_name_annotated_violation(self) -> None:
        """Test that the checker correctly reports an invalid const name annotated with Final."""
        src = """
        from typing import Final

        const_not_upper: Final = "it is not"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Constant name "{name}" should be in UPPER_CASE_WITH_UNDERSCORES format. '
            f'Suggested fix: "CONST_NOT_UPPER". '
            f"Constants should be all-uppercase words with each word separated by an underscore. A "
            f"single leading underscore can be used to denote a private constant."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_const_name_underscore(self) -> None:
        """Test that the checker does not report a const name that starts with an underscore."""
        src = """
        _MY_PRIVATE_CONST = "it is not"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_const_name_list(self) -> None:
        """Test that the checker does not report a const name that is assigned to a list."""
        src = """
        MY_CONSTANT_LIST = [1, 2, 3]
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_const_name_length_violation(self) -> None:
        """Test that the checker correctly reports a constant name that exceeds the maximum length."""
        src = """
        NAME_MORE_THAN_20_CHARACTERS = "too long"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = f'Constant name "{name}" exceeds the limit of 20 characters.'

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid class name."""
        src = """
        class notPascalcase:
            pass
        """
        mod = astroid.parse(src)
        classdef_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        name = classdef_node.name
        msg = (
            f'Class name "{name}" should be in PascalCase format. '
            f'Suggested fix: "NotPascalcase". '
            f"Class names should have the first letter of each word capitalized with no separation "
            f"between each word. A single leading underscore can be used to denote a private class."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=classdef_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(classdef_node)

    def test_class_name_alias_violation(self) -> None:
        """Test that the checker correctly reports an invalid class name."""
        src = """
        class MyClass:
            pass

        snake_case = MyClass
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Class name "{name}" should be in PascalCase format. '
            f'Suggested fix: "SnakeCase". '
            f"Class names should have the first letter of each word capitalized with no separation "
            f"between each word. A single leading underscore can be used to denote a private class."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_name_underscore(self) -> None:
        """Test that the checker does not report a class name that starts with an underscore."""
        src = """
        class _MyClass:
            pass
        """
        mod = astroid.parse(src)
        classdef_node, *_ = mod.nodes_of_class(nodes.ClassDef)

        with self.assertNoMessages():
            self.checker.visit_classdef(classdef_node)

    def test_function_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid function name."""
        src = """
        def NotSnakeCase():
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        name = functiondef_node.name
        msg = (
            f'Function name "{name}" should be in snake_case format. '
            f'Suggested fix: "not_snake_case". '
            f"Function names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private function."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=functiondef_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(functiondef_node)

    def test_function_name_underscore(self) -> None:
        """Test that the checker does not report a function name that starts with an underscore."""
        src = """
        def _my_function():
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(functiondef_node)

    def test_method_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid method name."""
        src = """
        class BadClass:
            def AlsoAlsoNotSnakeCase(self):
                pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        name = functiondef_node.name
        msg = (
            f'Method name "{name}" should be in snake_case format. '
            f'Suggested fix: "also_also_not_snake_case". '
            f"Method names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private method while "
            f"a double leading underscore invokes Python's name-mangling rules."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=functiondef_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(functiondef_node)

    def test_method_name_underscore(self) -> None:
        """Test that the checker does not report a method name that starts with an underscore."""
        src = """
        class BadClass:
            def _my_function(self):
                pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(functiondef_node)

    def test_method_name_override(self) -> None:
        """Test that a checker does not report an overridden method name."""
        src = """
        from typing import override

        class ParentClass:
            def AlsoNotSnakeCase(self):
                pass

        class BadClass(ParentClass):
            @override
            def AlsoNotSnakeCase(self):
                pass
        """

        mod = astroid.parse(src)
        _, functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(functiondef_node)

    def test_attr_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid attr name."""
        src = """
        class BadClass:
            AlsoNotSnakeCase: str
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Attribute name "{name}" should be in snake_case format. '
            f'Suggested fix: "also_not_snake_case". '
            f"Attribute names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private attribute while "
            f"a double leading underscore invokes Python's name-mangling rules."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_attr_name_underscore(self) -> None:
        """Test that the checker does not report an attribute name that starts with an underscore."""
        src = """
        class GoodClass:
            _attr: str
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_argument_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid argument name."""
        src = """
        def bad(AlsoNotSnakeCase):
            pass
        """
        mod = astroid.parse(src)
        argument_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = argument_node.name
        msg = (
            f'Argument name "{name}" should be in snake_case format. '
            f'Suggested fix: "also_not_snake_case". '
            f"Argument names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to indicate that the argument is "
            f"not being used but is still needed somehow."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=argument_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(argument_node)

    def test_argument_name_underscore(self) -> None:
        """Test that the checker does not report an argument name that starts with an underscore."""
        src = """
        def good(_name: str) -> None:
            print(_name)
        """
        mod = astroid.parse(src)
        argument_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(argument_node)

    def test_argument_name_length(self) -> None:
        """Test that the checker does not report an argument name that is longer than
        the default limit but shorter than the configured limit."""
        src = """
        def good(longer_than_30_chars_but_still_valid: str) -> None:
            pass
        """
        mod = astroid.parse(src)
        argument_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(argument_node)

    def test_variable_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid variable name."""
        src = """
        def foo():
            whyIsThisNotInSnakeCase = "idk"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Variable name "{name}" should be in snake_case format. '
            f'Suggested fix: "why_is_this_not_in_snake_case". '
            f"Variable names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private variable."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_variable_name_redefined_import_violation(self) -> None:
        """Test that the checker correctly reports an invalid variable name with import redefinition."""
        src = """
        try:
            import notSnakeCase
        except ImportError:
            notSnakeCase = None
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Variable name "{name}" should be in snake_case format. '
            f'Suggested fix: "not_snake_case". '
            f"Variable names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private variable."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_variable_name_comprehension_violation(self) -> None:
        """Test that the checker reports an invalid name used as a comprehension target."""
        src = """
        def foo():
            return [BadName for BadName in range(3)]
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Variable name "{name}" should be in snake_case format. '
            f'Suggested fix: "bad_name". '
            f"Variable names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private variable."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_variable_name_leading_underscore(self) -> None:
        """Test that the checker does not report a variable name that starts with an underscore."""
        src = """
        def f():
            _my_var = 10
            print(_my_var)
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_variable_name_underscore(self) -> None:
        """Test that the checker does not report a variable name that is just an underscore."""
        src = """
        for _ in range(10):
            print('hi')
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_variable_name_first_char_violation(self) -> None:
        """Test that the checker correctly reports a variable name that starts with a non-letter character
        and does not provide a suggested fix."""
        src = """
        def f():
            _9bad_name = 10
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Variable name "{name}" should be in snake_case format. '
            f"Variable names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private variable."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_attribute_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid class attribute name."""
        src = """
        class BadClass:
            notSNAKING = "CONSTANT"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Class attribute name "{name}" should be in snake_case format. '
            f'Suggested fix: "not_snaking". '
            f"Class attribute names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private class attribute while "
            f"a double leading underscore invokes Python's name-mangling rules."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_attribute_name_classvar_violation(self) -> None:
        """Test that the checker correctly reports an invalid class attribute name annotated with ClassVar."""
        src = """
        from typing import ClassVar

        class BadClass:
            notSNAKING: ClassVar = "CONSTANT"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Class attribute name "{name}" should be in snake_case format. '
            f'Suggested fix: "not_snaking". '
            f"Class attribute names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private class attribute while "
            f"a double leading underscore invokes Python's name-mangling rules."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_attribute_name_underscore(self) -> None:
        """Test that the checker does not report a class attribute name that starts with an
        underscore."""
        src = """
        from typing import ClassVar

        class BadClass:
            _snake_case: ClassVar = "CONSTANT"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_class_attribute_name_length(self) -> None:
        """Test that the checker does not report a class attribute name that is longer than
        the default limit but shorter than the configured limit."""
        src = """
        class MyClass:
            a_very_long_class_attribute_name = "CONSTANT"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_class_const_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid class constant name."""
        src = """
        from typing import Final

        class BadClass:
            ooga_booga: Final = "yo"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Class constant name "{name}" should be in UPPER_CASE_WITH_UNDERSCORES format. '
            f'Suggested fix: "OOGA_BOOGA". '
            f"Constants should be all-uppercase words with each word separated by an "
            f"underscore. A single leading underscore can be used to denote a private "
            f"constant. A double leading underscore invokes Python's name-mangling rules."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_const_name_underscore(self) -> None:
        """Test that the checker does not report a class constant name that starts with an
        underscore."""
        src = """
        from typing import Final

        class BadClass:
            _MY_CONSTANT: Final = "CONSTANT"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_typevar_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid typevar name."""
        src = """
        from typing import TypeVar

        type_var = TypeVar('type_var', str, float)
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Type variable name "{name}" should be in PascalCase format. '
            f'Suggested fix: "TypeVar". '
            f"Type variable names should have the first letter of each word capitalized with "
            f"no separation between each word."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_typevar_name_tuple_violation(self) -> None:
        """Test that the checker correctly reports an invalid typevar name in a tuple."""
        src = """
        from typing import TypeVar

        SOME_CONSTANT, type_var = 10, TypeVar('type_var', str)
        """
        mod = astroid.parse(src)
        _, assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Type variable name "{name}" should be in PascalCase format. '
            f'Suggested fix: "TypeVar". '
            f"Type variable names should have the first letter of each word capitalized with "
            f"no separation between each word."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_typevar_name_underscore(self) -> None:
        """Test that the checker does not report a typevar name that starts with an underscore."""
        src = """
        from typing import TypeVar

        _MyTypeVar = TypeVar('type_var', str, float)
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    @unittest.skipIf(sys.version_info < (3, 10, 0), "TypeAlias was new in version 3.10.")
    def test_typealias_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid typealias name."""
        src = """
        from typing import TypeAlias

        not_pascal: TypeAlias = dict, str
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Type alias name "{name}" should be in PascalCase format. '
            f'Suggested fix: "NotPascal". '
            f"Type alias names should have the first letter of each word capitalized with "
            f"no separation between each word."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    @unittest.skipIf(sys.version_info < (3, 10, 0), "TypeAlias was new in version 3.10.")
    def test_typealias_name_union_violation(self) -> None:
        """Test that the checker correctly reports an invalid Union typealias name."""
        src = """
        from typing import Union

        not_pascal = Union[dict, str]
        """

        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Type alias name "{name}" should be in PascalCase format. '
            f'Suggested fix: "NotPascal". '
            f"Type alias names should have the first letter of each word capitalized with "
            f"no separation between each word."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    @unittest.skipIf(sys.version_info < (3, 10, 0), "TypeAlias was new in version 3.10.")
    def test_typealias_name_tuple_violation(self) -> None:
        """Test that the checker correctly reports an invalid typealias name in a tuple."""
        src = """
        from typing import TypeAlias

        SOME_CONSTANT, not_pascal = 10, TypeAlias
        """

        mod = astroid.parse(src)
        _, assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Type alias name "{name}" should be in PascalCase format. '
            f'Suggested fix: "NotPascal". '
            f"Type alias names should have the first letter of each word capitalized with "
            f"no separation between each word."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    @unittest.skipIf(sys.version_info < (3, 10, 0), "TypeAlias was new in version 3.10.")
    def test_typealias_name_underscore(self) -> None:
        """Test that the checker does not report a type alias name that starts with an underscore."""
        src = """
        from typing import TypeAlias

        _MyTypeAlias: TypeAlias = dict, str
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    @unittest.skipIf(sys.version_info < (3, 10, 0), "TypeAlias was new in version 3.10.")
    def test_typealias_name_length_violation(self) -> None:
        """Test that the checker correctly reports a type alias name that exceeds the maximum length."""
        src = """
        from typing import TypeAlias

        NameThatIsTooLong: TypeAlias = dict, str
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = f'Type alias name "{name}" exceeds the limit of 15 characters.'

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_name_in_main_block(self) -> None:
        """Test that the checker does not report a top-level variable that is assigned within
        a main block."""
        src = """
        if __name__ == '__main__':
            const_not_upper = "it is not"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_ignore_function_name(self):
        """Test that the checker does not report an invalid function name that matches
        at least one of the patterns in ignore-names
        """
        src = """
        def ignored_very_long_function_name():
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(functiondef_node)

    def test_ignore_class_name(self):
        """Test that the checker does not report an invalid function name that matches
        at least one of the patterns in ignore-names
        """
        src = """
        class ignored_invalid_class_name():
            pass
        """
        mod = astroid.parse(src)
        classdef_node, *_ = mod.nodes_of_class(nodes.ClassDef)

        with self.assertNoMessages():
            self.checker.visit_classdef(classdef_node)

    def test_ignore_variable_name(self):
        """Test that the checker does not report an invalid variable name that matches
        at least one of the patterns in ignore-names"""
        src = """
        def func():
            ignoredInvalidVariableName = 10
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)

        with self.assertNoMessages():
            self.checker.visit_assignname(assignname_node)

    def test_ignore_module_name(self):
        """Test that the checker does not report an error when the module has an invalid name,
        but it matches at least one of the pattens in ignore-module-names.
        """
        src = """
        i = "hi"
        """
        mod = astroid.parse(src)
        module_node, *_ = mod.nodes_of_class(nodes.Module)
        module_node.name = "ignored_InvalidModuleName"

        with self.assertNoMessages():
            self.checker.visit_module(module_node)


class TestInvalidNameCheckerDefaultConfig(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidNameChecker

    def set_up(self) -> None:
        """Perform the set up before each test case executes."""
        self.setup_method()

    def test_default_ignore_module_names_invalid(self):
        """Test that the checker correctly reports an invalid module name
        with the default configuration options.
        """
        src = """
        i = "test module"
        """
        mod = astroid.parse(src)
        module_node, *_ = mod.nodes_of_class(nodes.Module)
        module_node.name = "InvalidModuleName"
        msg = (
            f'Module name "{module_node.name}" should be in snake_case format. '
            f'Suggested fix: "invalid_module_name". '
            f"Modules should be all-lowercase names, with each name separated by underscores."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="module-name-violation", node=module_node, args=msg, line=1
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(module_node)

    def test_default_ignore_module_names_valid(self):
        """Test that the checker does not report an error for valid module names
        with the default configuration option.
        """
        src = """
        i = "test module"
        """
        mod = astroid.parse(src)
        module_node, *_ = mod.nodes_of_class(nodes.Module)
        module_node.name = "valid_module_name"

        with self.assertNoMessages():
            self.checker.visit_module(module_node)

    def test_default_ignore_names_invalid(self):
        """Test that the checker correctly reports an invalid name
        with the default configuration options.
        """
        src = """
        def NotSnakeCase():
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        name = functiondef_node.name
        msg = (
            f'Function name "{name}" should be in snake_case format. '
            f'Suggested fix: "not_snake_case". '
            f"Function names should be lowercase, with words separated by underscores. "
            f"A single leading underscore can be used to denote a private function."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=functiondef_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(functiondef_node)

    def test_default_ignore_names_valid(self):
        """Test that the checker does not report an error for valid names
        with the default configuration option.
        """
        src = """
        def snake_case_format():
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(functiondef_node)

    def test_default_module_length_violation(self) -> None:
        """Test that the checker correctly reports a module name that's longer than the default
        limit of 30 characters."""
        src = """
        i = "test module"
        """
        mod = astroid.parse(src)
        module_node, *_ = mod.nodes_of_class(nodes.Module)
        module_node.name = "abc" * 11
        msg = f'Module name "{module_node.name}" exceeds the limit of 30 characters.'

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="module-name-violation", node=module_node, args=msg, line=1
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(module_node)

    def test_default_class_name_length_no_violation(self) -> None:
        """Test that the checker does not report an error for a class name that's shorter than the
        default limit of 30 characters."""
        src = """
        class ClassNameThatIsNotTooLong:
            pass
        """
        mod = astroid.parse(src)
        classdef_node, *_ = mod.nodes_of_class(nodes.ClassDef)

        with self.assertNoMessages():
            self.checker.visit_classdef(classdef_node)

    def test_default_function_name_length_violation(self) -> None:
        """Test that the checker correctly reports a function name that's longer than the default
        limit of 30 characters."""
        long_name = "a" * 31
        src = f"""
        def {long_name}():
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        msg = f'Function name "{long_name}" exceeds the limit of 30 characters.'

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=functiondef_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(functiondef_node)

    def test_default_typevar_name_length_violation(self) -> None:
        """Test that the checker correctly reports a type variable name that's longer than the default
        limit of 20 characters."""
        long_name = "Aa" * 11
        src = f"""
        from typing import TypeVar

        {long_name} = TypeVar('{long_name}')
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        msg = f'Type variable name "{long_name}" exceeds the limit of 20 characters.'

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=assignname_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)


def test_module_name_no_snippet() -> None:
    """Test that PythonTA does not build a snippet for the message added by this checker."""
    curr_dir = os.path.dirname(__file__)
    file_fixture = os.path.join(curr_dir, "file_fixtures", "badModuleName.py")
    config = os.path.join(os.path.dirname(curr_dir), "test.pylintrc")
    reporter = python_ta.check_all(module_name=file_fixture, config=config)

    snippet = reporter.messages[file_fixture][0].snippet

    assert snippet == ""


class TestNamingConventionHelpers(unittest.TestCase):
    def test_to_pascal_case(self) -> None:
        """Test that names are correctly converted to PascalCase."""
        self.assertEqual(_to_pascal_case("snake_case"), "SnakeCase")
        self.assertEqual(_to_pascal_case("PascalCase"), "PascalCase")
        self.assertEqual(_to_pascal_case("_UPPER_CASE_NAME"), "_UPPERCASENAME")
        self.assertEqual(_to_pascal_case("__varName_here_"), "_VarNameHere")
        self.assertEqual(_to_pascal_case("parseJSONText"), "ParseJSONText")

    def test_to_uppercase_with_underscores(self) -> None:
        """Test that names are correctly converted to UPPERCASE_WITH_UNDERSCORES."""
        self.assertEqual(_to_upper_case_with_underscores("snake_case"), "SNAKE_CASE")
        self.assertEqual(_to_upper_case_with_underscores("PascalCase"), "PASCAL_CASE")
        self.assertEqual(_to_upper_case_with_underscores("_UPPER_CASE_NAME"), "_UPPER_CASE_NAME")
        self.assertEqual(_to_upper_case_with_underscores("__varName_here_"), "_VAR_NAME_HERE_")
        self.assertEqual(_to_upper_case_with_underscores("parseJSONText"), "PARSE_JSON_TEXT")

    def test_to_snake_case(self) -> None:
        """Test that names are correctly converted to snake_case."""
        self.assertEqual(_to_snake_case("snake_case"), "snake_case")
        self.assertEqual(_to_snake_case("PascalCase"), "pascal_case")
        self.assertEqual(_to_snake_case("UPPER_CASE_NAME"), "upper_case_name")
        self.assertEqual(_to_snake_case("_MIXED_CaseName"), "_mixed_case_name")
        self.assertEqual(_to_snake_case("_5first_char_non_letter"), None)
        self.assertEqual(
            _to_snake_case("_name_with_num_not_first_10"), "_name_with_num_not_first_10"
        )
