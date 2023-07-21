"""Test suite for testing the InvalidNameChecker."""

import astroid
import pylint.testutils
from astroid import nodes

from python_ta.checkers.invalid_name_checker import InvalidNameChecker


class TestInvalidNameChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidNameChecker
    CONFIG = {
        # To prevent a Namespace error.
        "property_classes": "",
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
        print(module_node.name)
        args = (
            "module",
            module_node.name,
            f'"{module_node.name}" is a single character name that should be avoided. In some '
            f"fonts, these characters are indistinguishable from the numbers 1 and 0.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-name-violation", node=module_node, args=args),
            ignore_position=True,
        ):
            self.checker.visit_module(module_node)

    def test_const_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid const name."""
        src = """
        const_not_upper = "it is not"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        args = (
            "const",
            name,
            f'Const name "{name}" is not in UPPER_CASE_WITH_UNDERSCORES. Constants should be '
            f"all-uppercase words with each word separated by an underscore. A single leading "
            f"underscore can be used to denote a private constant.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
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
        args = (
            "class",
            name,
            f'Class name "{name}" is not in PascalCase. Class names should have the '
            f"first letter of each word capitalized with no separation between each "
            f"word. A single leading underscore can be used to denote a private "
            f"class.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=classdef_node, args=args
            ),
            ignore_position=True,
        ):
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
        args = (
            "function",
            name,
            f'Function name "{name}" is not in snake_case. Function names should be lowercase, '
            f"with words separated by underscores. A single leading underscore can be used to "
            f"denote a private function.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=functiondef_node, args=args
            ),
            ignore_position=True,
        ):
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
        args = (
            "method",
            name,
            f'Method name "{name}" is not in snake_case. Method names should be lowercase, with '
            f"words separated by underscores. A single leading underscore can be used to denote a "
            f"private method while a double leading underscore invokes Python's name-mangling "
            f"rules.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=functiondef_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(functiondef_node)

    def test_attr_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid attr name."""
        src = """
        class BadClass:
            def __init__(self):
                self.AlsoNotSnakeCase = "no"
        """
        mod = astroid.parse(src)
        classdef_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        assignattr_node, *_ = mod.nodes_of_class(nodes.AssignAttr)
        args = (
            "attr",
            "AlsoNotSnakeCase",
            f'Attr name "AlsoNotSnakeCase" is not in snake_case. Attr names should be lowercase, '
            f"with words separated by underscores. A single leading underscore can be used to "
            f"denote a private attr while a double leading underscore invokes Python's "
            f"name-mangling rules.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignattr_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(classdef_node)

    def test_argument_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid argument name."""
        src = """
        def bad(l):
            pass
        """
        mod = astroid.parse(src)
        functiondef_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        argument_node = functiondef_node.args.args[0]
        name = argument_node.name
        args = (
            "argument",
            name,
            f'"{name}" is a single character name that should be avoided. In some fonts, these '
            f"characters are indistinguishable from the numbers 1 and 0.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=argument_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(functiondef_node)

    def test_variable_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid variable name."""
        src = """
        def foo():
            whyIsThisNotInSnakeCase = "idk"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        args = (
            "variable",
            name,
            f'Variable name "{name}" is not in snake_case. Variable names should be lowercase, '
            f"with words separated by underscores. A single leading underscore can be used to "
            f"denote a private variable.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
            ),
            ignore_position=True,
        ):
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
        args = (
            "class attribute",
            name,
            f'Class attribute name "{name}" is not in snake_case. Class attribute names should be '
            f"lowercase, with words separated by underscores. A single leading underscore can be "
            f"used to denote a private class attribute while a double leading underscore invokes "
            f"Python's name-mangling rules.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_class_const_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid class const name."""
        src = """
        from typing import Final

        class BadClass:
            ooga_booga: Final = "yo"
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        args = (
            "class const",
            name,
            f'Class const name "{name}" is not in UPPER_CASE_WITH_UNDERSCORES. Constants should be '
            f"all-uppercase words with each word separated by an underscore. A single leading "
            f"underscore can be used to denote a private constant.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_inlinevar_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid inlinevar name."""
        src = """
        [NO_SNAKE for NO_SNAKE in range(1, 3)]
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        args = (
            "inlinevar",
            name,
            f'Inline variable name "{name}" is not in snake_case. Inline variable names should be '
            f"lowercase, with words separated by underscores. A single underscore can be used to "
            f'denote a "throwaway"/unused variable.',
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
            ),
            ignore_position=True,
        ):
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
        args = (
            "typevar",
            name,
            f'Typevar name "{name}" does not abide by the naming convention. Typevar names may '
            f"start with 0-2 underscores, does not start with a capital T, and is either in all "
            f"capital letters and no underscores, or in PascalCase, optionally ending in T and not "
            f'ending with "Type", an optional "_co" or "_contra" ending.',
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)

    def test_typealias_name_violation(self) -> None:
        """Test that the checker correctly reports an invalid typealias name."""
        src = """
        from typing import TypeAlias

        not_pascal: TypeAlias = dict, str
        """
        mod = astroid.parse(src)
        assignname_node, *_ = mod.nodes_of_class(nodes.AssignName)
        name = assignname_node.name
        args = (
            "typealias",
            name,
            f'Typealias name "{name}" is not in PascalCase. Typealias names should have the first '
            f"letter of each word capitalized with no separation between each word.",
        )

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-name-violation", node=assignname_node, args=args
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(assignname_node)
