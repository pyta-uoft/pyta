import astroid
import pylint.testutils

from python_ta.checkers.global_variables_checker import GlobalVariablesChecker


class TestGlobalVariablesChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = GlobalVariablesChecker

    def test_no_message_global_type_alias_assignment_builtin(self):
        """Global type alias assignment allowed, no message."""
        src = """
        MyType = list[list[list[int]]]
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_assignname(mod)

    def test_message_global_type_alias_assignment_builtin(self):
        """Global type alias assignment not allowed, raises a message."""
        src = """
        TypeName = list[int]
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-global-variables",
                node=mod.globals["TypeName"][0],
                args="a global variable 'TypeName' is assigned to on line 2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_assignname(mod)

    def test_no_message_global_type_alias_assignment_import(self):
        """Global type alias assignment allowed, no message."""
        src = """
        import datetime
        MyType = datetime.date
        """
        mod = astroid.parse(src)
        attribute_node = [child for child in mod.body[1].get_children()][1]
        attribute_name_node = [child for child in attribute_node.get_children()][0]
        with self.assertNoMessages():
            self.checker.visit_import(mod.body[0])
            self.checker.visit_assignname(attribute_name_node)
