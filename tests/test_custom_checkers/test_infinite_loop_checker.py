import os

import astroid
import pylint.testutils

from python_ta.checkers.infinite_loop_checker import InfiniteLoopChecker


class TestInfiniteLoopChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InfiniteLoopChecker
    CONFIG = {
        "allowed_import_modules": ["python_ta"],
        "extra_imports": ["datetime", "math.floor"],
    }

    def test_tracked_vars(self) -> None:
        src = """
        i = 10
        while 10 < i < 20 and j > 10 and True or n == 21 and self.h > 19:
            i += 1
            i, j = i + 1, 21
            i = 10
            j += 1
            self.h = 21
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.While)

        self.checker.visit_while(node)
        self.checker.leave_while(node)

    def test_nested_while(self) -> None:
        src = """
        i = 0
        j = 10
        while i < 10:
            while j < 20:
                j += 1
                i = i - 1
            i += 2
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.While)

        self.checker.visit_while(node)
        self.checker.leave_while(node)

    def test_multiple_while(self) -> None:
        src = """
        i = 0
        j = 10
        while i < 10:
            i += 2
        while j < 20:
                j += 1
        """

        mod = astroid.parse(src)

        for node in mod.nodes_of_class(astroid.nodes.While):
            self.checker.visit_while(node)
            self.checker.leave_while(node)
