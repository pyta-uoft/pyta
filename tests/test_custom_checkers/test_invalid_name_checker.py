"""Test suite for testing the InvalidNameChecker."""
import os
import sys
import unittest

import astroid
import pylint.testutils
from astroid import nodes

import python_ta
from python_ta.checkers.invalid_name_checker import InvalidNameChecker


class TestInvalidNameChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidNameChecker

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
            f'Constant name "{name}" should be in UPPER_CASE_WITH_UNDERSCORES format. Constants '
            f"should be all-uppercase words with each word separated by an underscore. A "
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
            f'Class name "{name}" should be in PascalCase format. Class names should have the '
            f"first letter of each word capitalized with no separation between each word. A "
            f"single leading underscore can be used to denote a private class."
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="naming-convention-violation", node=classdef_node, args=msg
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(classdef_node)

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
            f'Function name "{name}" should be in snake_case format. Function names should be '
            f"lowercase, with words separated by underscores. A single leading underscore can "
            f"be used to denote a private function."
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
            f'Method name "{name}" should be in snake_case format. Method names should be '
            f"lowercase, with words separated by underscores. A single leading underscore can "
            f"be used to denote a private method while a double leading underscore invokes "
            f"Python's name-mangling rules."
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
            f'Attribute name "{name}" should be in snake_case format. Attribute names should be '
            f"lowercase, with words separated by underscores. A single leading underscore can "
            f"be used to denote a private attribute while a double leading underscore invokes "
            f"Python's name-mangling rules."
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
        def bad(l):
            pass
        """
        mod = astroid.parse(src)
        argument_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = argument_node.name
        msg = (
            f'"{name}" is a name that should be avoided. Change to something less ambiguous '
            f"and/or more descriptive."
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
            f'Variable name "{name}" should be in snake_case format. Variable names should be '
            f"lowercase, with words separated by underscores. A single leading underscore can "
            f"be used to denote a private variable."
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

    def test_class_attribute_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid class attribute name."""
        src = """
        from typing import ClassVar

        class BadClass:
            notSNAKING: ClassVar = "CONSTANT"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        msg = (
            f'Class attribute name "{name}" should be in snake_case format. Class attribute names '
            f"should be lowercase, with words separated by underscores. A single leading "
            f"underscore can be used to denote a private class attribute while a double "
            f"leading underscore invokes Python's name-mangling rules."
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
            f'Type variable name "{name}" should be in PascalCase format. Type variable names '
            f"should have the first letter of each word capitalized with no separation between "
            f"each word."
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
            f'Type alias name "{name}" should be in PascalCase format. Type alias names should '
            f"have the first letter of each word capitalized with no separation between each "
            f"word."
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


def test_module_name_no_snippet() -> None:
    """Test that PythonTA does not build a snippet for the message added by this checker."""
    curr_dir = os.path.dirname(__file__)
    file_fixture = os.path.join(curr_dir, "file_fixtures", "badModuleName.py")
    reporter = python_ta.check_all(module_name=file_fixture)

    snippet = reporter.messages[file_fixture][0].snippet

    assert snippet == ""
