import pylint.testutils
import astroid
from python_ta.checkers.missing_space_in_doctest_checker import MissingSpaceInDoctestChecker


class TestMissingSpaceInDoctestChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = MissingSpaceInDoctestChecker

    def setUp(self):
        self.setup_method()

    def test_missing_space(self) -> None:
        """Test the checker on a doctest missing a space"""
        src = '''
        def f(x: int) -> int:
            """Return one plus x.
        
            >>>f(10)  #@
            11
            """
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='missing-space-in-doctest',
                    node=function_node,
                    args=function_node.name,
                    line=5
                )
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_missing_space(self) -> None:
        """Test the checker on a doctest not missing the space"""
        src = '''
        def f(x: int) -> int:
            """Return one plus x.

            >>> f(10)  
            11
            """
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_missing_space_multiple(self) -> None:
        """Test the checker on multiple doctests missing spaces"""
        src = '''
        def f(x: int) -> int:
            """Return one plus x.

            >>>f(10)  #@
            11
            >>>f(11)  #@
            12
            """
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='missing-space-in-doctest',
                    node=function_node,
                    args=function_node.name,
                    line=5
                ),
                pylint.testutils.Message(
                    msg_id='missing-space-in-doctest',
                    node=function_node,
                    args=function_node.name,
                    line=7
                )
        ):
            self.checker.visit_functiondef(function_node)

    def test_missing_space_mixed(self) -> None:
        """Test the checker on multiple doctests"""
        src = '''
        def f(x: int) -> int:
            """Return one plus x.

            >>> f(10) 
            11
            >>>f(11)  #@
            12
            """
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='missing-space-in-doctest',
                    node=function_node,
                    args=function_node.name,
                    line=7
                )
        ):
            self.checker.visit_functiondef(function_node)

    def test_empty_docstring(self) -> None:
        """Test the checker on a function with an empty docstring so it does not
        raise an error"""
        src = '''
           def f(x: int) -> int:
               """
               """
           '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_no_docstring(self) -> None:
        """Test the checker on a function with no docstring so it does not
        raise an error"""
        src = '''
           def f(x: int) -> int:
                pass
           '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_no_doctests(self) -> None:
        """Test the checker on a function with no doctests in the docstring"""
        src = '''
           def f(x: int) -> int:
               """Return one plus x.
               """
           '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_only_doctest_marker(self) -> None:
        """Test the checker only containing the doctest marker"""
        src = '''
              def f(x: int) -> int:
                  """>>>"""
              '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='missing-space-in-doctest',
                    node=function_node,
                    args=function_node.name,
                    line=3
                )
        ):
            self.checker.visit_functiondef(function_node)

    def test_not_valid(self) -> None:
        """Test the checker so that it does not recognize the doctest symbol
        if not at the start of the line"""
        src = '''
           def f(x: int) -> int:
               """Return one plus x.
               
               abc >>> 123 
               
               abc >>>1 + 2 
               
               123>>>456 
               """
           '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(astroid.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)


if __name__ == "__main__":
    import pytest
    pytest.main(['test_missing_space_in_doctest_checker.py'])
