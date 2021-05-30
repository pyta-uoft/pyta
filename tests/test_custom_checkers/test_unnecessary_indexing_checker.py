import pylint.testutils
import astroid
from python_ta.checkers.unnecessary_indexing_checker import UnnecessaryIndexingChecker
from python_ta.cfg import CFGVisitor


class TestUnnecessaryIndexingChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = UnnecessaryIndexingChecker

    def setUp(self):
        self.setup_method()

    def test_runtime_error(self):
        src = """
        def f(lst: list) -> None:
            i = 0
            for i in range(len(lst)):
                if lst[0]:
                    i = 1
                else:
                    i = 2
        """
        mod = astroid.parse(src)
