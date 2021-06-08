import pylint.testutils
import astroid
from python_ta.checkers.unnecessary_indexing_checker import UnnecessaryIndexingChecker


class TestUnnecessaryIndexingChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = UnnecessaryIndexingChecker

    def setUp(self):
        self.setup_method()

    def test_empty_scope_no_message(self):
        """The AssignName node i = 2 returns (builtins, ()) for the scope
        """
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
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_sum_items_msg(self):
        src = """
        def sum_items(lst: List[int]) -> int:
            s = 0
            for i in range(len(lst)):  #@
                s += lst[i]
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='unnecessary-indexing',
                    node=for_node.target,
                    args=for_node.target.name
                )
        ):
            self.checker.visit_for(for_node)

    def test_sum_items2_msg(self):
        src = """
        def sum_items2(lst: List[int]) -> int:
            s = 0
            for i in range(0, len(lst)):  #@
                s += lst[i]
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='unnecessary-indexing',
                    node=for_node.target,
                    args=for_node.target.name
                )
        ):
            self.checker.visit_for(for_node)

    def test_sum_items3_msg(self):
        src = """
        def sum_items3(lst: List[int]) -> int:
            s = 0
            for i in range(0, len(lst), 1):  #@
                s += lst[i]
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='unnecessary-indexing',
                    node=for_node.target,
                    args=for_node.target.name
                )
        ):
            self.checker.visit_for(for_node)

    def test_sum_pairs_no_message(self):
        """NO error reported; the loop index is used to index lst2 as well."""
        src = """
        def sum_pairs(lst1: List[int], lst2: List[int]) -> int:
            s = 0
            for i in range(len(lst1)):
                s += lst1[i] * lst2[i]
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_nested_sum_msg(self):
        src = """
        def nested_sum(items: List[List[int]]) -> int:
            s = 0
            for i in range(len(items)):  #@
                s += sum([2 * x for x in items[i]])
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='unnecessary-indexing',
                    node=for_node.target,
                    args=for_node.target.name
                )
        ):
            self.checker.visit_for(for_node)

    def test_nested_comprehension_msg(self):
        src = """
        def nested_comprehension(items: list) -> None:
            for i in range(len(items)):  #@
                print([[items[i] for _ in range(10)] for _ in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='unnecessary-indexing',
                    node=for_node.target,
                    args=for_node.target.name
                )
        ):
            self.checker.visit_for(for_node)

    def test_nested_comprehensions2_no_message(self):
        """NO error reported; j is initialized outside the loop"""
        src = """
        def nested_comprehensions2(items: list) -> None:
            j = 0
            for _ in range(len(items)):
                print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_nested_comprehensions3_no_message(self):
        """NO error reported; j is undefined."""
        src = """
        def nested_comprehensions3(items: list) -> None:
            for _ in range(len(items)):
                print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_nested_comprehensions4_no_message(self):
        """NO error reported; j is undefined."""
        src = """
        def nested_comprehensions3(items: list) -> None:
            for _ in range(len(items)):
                print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_loop_variable_reassigned_no_message(self):
        """NO error reported; the loop variable assignment i is unused,
        but is not redundant."""
        src = """
        def loop_variable_reassigned(items: List[int]) -> int:
            s = 0
            for i in range(len(items)):
                i = 0
                s += items[i]
            
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)


if __name__ == "__main__":
    import pytest
    pytest.main(['test_unnecessary_indexing_checker.py'])
