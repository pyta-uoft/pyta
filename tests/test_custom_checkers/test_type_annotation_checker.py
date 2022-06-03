import astroid
import pylint.testutils
from astroid import nodes

from python_ta.checkers.type_annotation_checker import TypeAnnotationChecker


class TestTypeAnnotationChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = TypeAnnotationChecker

    def test_type_is_assigned_for_function(self):
        """Ensure that checker catches when type is assigned instead of annotated
        in function parameters."""
        src = """
        def add_two_numbers(x=int, y=int) -> int:
            # type is assigned instead of annotated here,
            # should be def add_two_numbers(x: int, y: int) -> int
            return x + y
        """
        function_def = astroid.extract_node(src)
        arg_node_x = function_def.args.find_argname("x")[1]
        arg_node_y = function_def.args.find_argname("y")[1]
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="type-is-assigned",
                node=arg_node_x,
            ),
            pylint.testutils.MessageTest(
                msg_id="type-is-assigned",
                node=arg_node_y,
            ),
            pylint.testutils.MessageTest(
                msg_id="missing-param-type",
                node=arg_node_x,
            ),
            pylint.testutils.MessageTest(
                msg_id="missing-param-type",
                node=arg_node_y,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_def)

    def test_type_is_assigned_for_class(self):
        """Ensure that checker catches when type is assigned instead of annotated
        in class attributes."""
        src = """
        class MyDataType:
            # type is assigned instead of annotated here
            x = int
            y = int
        """
        class_def = astroid.extract_node(src)
        attr_node_x = class_def.locals["x"][0]
        attr_node_y = class_def.locals["y"][0]
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-attribute-type",
                node=attr_node_x,
            ),
            pylint.testutils.MessageTest(
                msg_id="type-is-assigned",
                node=attr_node_x,
            ),
            pylint.testutils.MessageTest(
                msg_id="missing-attribute-type",
                node=attr_node_y,
            ),
            pylint.testutils.MessageTest(
                msg_id="type-is-assigned",
                node=attr_node_y,
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_def)
