import pylint.testutils
import astroid
from python_ta.checkers.unnecessary_indexing_checker import UnnecessaryIndexingChecker


class TestUnnecessaryIndexingChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = UnnecessaryIndexingChecker

    def setUp(self):
        self.setup_method()

    def test_empty_scope_no_msg(self):
        """The AssignName node i = 2 returns (builtins, ()) for the scope"""
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
        """Return the sum of a list of numbers."""
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
        """Return the sum of a list of numbers."""
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
        """Return the sum of a list of numbers."""
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

    def test_sum_pairs_no_msg(self):
        """Return the sum of corresponding products of two list of numbers.

        NO error reported; the loop index is used to index lst2 as well."""
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
        """Return a repeated sum of the items in the list."""
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
        """Illustrate this checker in a nested comprehension."""
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

    def test_nested_comprehensions2_no_msg(self):
        """Illustrate this checker in a nested comprehension, where the
        loop variable is unused.

        NO error reported; j is initialized outside the loop"""
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

    def test_nested_comprehensions3_no_msg(self):
        """Illustrate this checker in a nested comprehension,
        where the index into the list is not defined.

        NO error reported; j is undefined."""
        src = """
        def nested_comprehensions3(items: list) -> None:
            for _ in range(len(items)):
                print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_nested_comprehensions4_no_msg(self):
        """Illustrate this checker in a nested comprehension,
        where the index into the list is defined in an outer comprehension.

        NO error reported; j is undefined."""
        src = """
        def nested_comprehensions4(items: list) -> None:
            for _ in range(len(items)):
                print([[items[j] for _ in range(10)] for j in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_loop_variable_reassigned_no_msg(self):
        """Illustrate this checker on a loop where the loop variable is reassigned
        in the loop body.

        NO error reported; the loop variable assignment i is unused,
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

    def test_sum_items_no_msg(self):
        """Elements are accessed directly, no unnecessary indexing"""
        src = """
        def sum_items(items: List[int]) -> int: 
            s = 0
            for x in items:
               s += x
            return s 
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_iter_var_unused_no_msg(self):
        """Iteration variable i is unused in the code, no unnecessary indexing performed"""
        src = """
        def iter_var_unused(items: List[int]) -> int: 
            s = 0 
            for i in range(len(items)):
                s += 1 
            return s 
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_comp_shadow_no_msg(self):
        """Iteration variable i is shadowed in the comprehension but not redundant"""
        src = """
        def f(lst):
            s = 0
            for i in range(len(lst)):
                lst = [i for i in range(i)]
                for x in lst:
                    s += x
            return s
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_assignname1_no_msg(self):
        """Iteration variable reassigned and used to increment

        Indexing the iterable is not the only usage"""
        src = """
        s = 0 
        for i in range(len(lst)):
            i = 0 
            s += i 
            print(items[i])
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_assignname2_no_msg(self):
        """Iteration variable incremented each iteration but unused"""
        src = """
        for i in range(len(lst)): 
            i += 10
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_augassign_no_msg(self):
        """The list is indexed every iteration but the value is being incremented

        Subscript is being used in a store context, so it is not redundant"""
        src = """
        for i in range(len(lst)): 
            lst[i] += 1
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(astroid.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)


if __name__ == "__main__":
    import pytest
    pytest.main(['test_unnecessary_indexing_checker.py'])
