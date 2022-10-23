import astroid
import pylint.testutils
from astroid import nodes

from python_ta.checkers.top_level_code_checker import TopLevelCodeChecker


class TestTopLevelCodeChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = TopLevelCodeChecker
    CONFIG = {}

    def setup(self):
        self.setup_method()

    def test_message_global(self):
        """Top level code not allowed, raises a message."""
        src = """
        print("testing code")
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod, args=mod.body
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)
