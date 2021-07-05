import pylint.testutils
import astroid
from python_ta.checkers.shadowing_in_comprehension_checker import ShadowingInComprehensionChecker


class TestShadowingInComprehensionChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ShadowingInComprehensionChecker

    def setUp(self):
        self.setup_method()

    def test_underscore_var1(self):
        """Test checker with _ usages"""
        src = """
        def nested_comprehensions3(items: list) -> None:
            for _ in range(len(items)):
                print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])
        """
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_underscore_var2(self):
        """Test checker with _ usages"""
        src = """
        for _ in range(len(items)):
            print([items[j] for _ in range(10)])
        """
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_underscore_var3(self):
        """Test checker with _ usages"""
        src = """
        _ = 2
        print({_ for _ in range(10)})
        """
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_underscore_var4(self):
        """Test checker with _ usages in a comp with a tuple target"""
        src = '''
        def switch_dict(_: dict) -> dict:
            return {y: _ for _, y in _.items()}
        '''
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_list_comp(self):
        """Test checker with a list comprehension
        """
        src = '''
        def num_lst(n: int) -> List[int]:
            """Return a list of integers from 0 to <n>, in that order."""
            return [n for n in range(n)]
        '''
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='shadowing-in-comprehension',
                    node=comp_node.target,
                    args=comp_node.target.name
                )
        ):
            self.checker.visit_comprehension(comp_node)

    def test_dict_comp(self):
        """Test checker with a dict comp containing a tuple target
        """
        src = '''
        def switch_dict(x: dict) -> dict:
            """Return a dictionary with keys and values switched."""
            return {y: x for x, y in x.items()}
        '''
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='shadowing-in-comprehension',
                    node=comp_node.target.elts[0],
                    args=comp_node.target.elts[0].name
                )
        ):
            self.checker.visit_comprehension(comp_node)

    def test_common_items(self):
        """Test checker with a set comp
        """
        src = '''
        def common_items(lst1: list, lst2: list) -> int:
            """Return the number of unique common items in <lst1> and <lst2>."""
            s = 0
            set1 = {s for s in lst1}
            for item in set1:
                if item in lst2:
                    s += 1
        
            return s
        '''
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='shadowing-in-comprehension',
                    node=comp_node.target,
                    args=comp_node.target.name
                )
        ):
            self.checker.visit_comprehension(comp_node)

    def test_print_pos(self):
        """Test checker with a generator
        """
        src = '''      
        def print_pos(lst: List[int]) -> None:
            """Print items in lst one by one if they are greater than 0."""
            for k in (k for k in lst if k > 0):
                print(k)
        '''
        mod = astroid.parse(src)
        comp_node, *_ = mod.nodes_of_class(astroid.Comprehension)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='shadowing-in-comprehension',
                    node=comp_node.target,
                    args=comp_node.target.name
                )
        ):
            self.checker.visit_comprehension(comp_node)


if __name__ == "__main__":
    import pytest
    pytest.main(['test_shadowing_in_comprehension_checker.py'])
