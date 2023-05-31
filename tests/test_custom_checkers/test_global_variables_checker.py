import astroid
import pylint.testutils

from python_ta.checkers.global_variables_checker import GlobalVariablesChecker


class TestGlobalVariablesChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = GlobalVariablesChecker

    def test_no_message_global_type_alias_assignment(self):
        """Global type alias assignment allowed, no message."""
        src = """
        MyType = list[list[list[int]]]
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_assignname(mod)

    def test_message_global_type_alias_assignment(self):
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
