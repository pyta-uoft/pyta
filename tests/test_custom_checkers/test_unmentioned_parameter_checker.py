import astroid
import pylint.testutils
from astroid import nodes

from python_ta.checkers.unmentioned_parameter_checker import \
    UnmentionedParameterChecker


class TestUnmentionedParameterChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = UnmentionedParameterChecker

    def setUp(self):
        self.setup_method()

    def test_no_missing_parameter(self) -> None:
        """Test the checker on a function with no missing parameters"""
        src = '''
                def f(x: int) -> int:
                    """Return one plus x
                    """
                    pass
                '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_no_missing_parameters_multiple(self) -> None:
        """Test a function with multiple parameters and no missing parameters"""
        src = '''
        def f(x: int, y: int) -> int:
            """Return x plus y

            >>> f(1, 2)
            3
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_missing_parameter(self) -> None:
        """Test the checker on a function with a missing parameter"""
        src = '''
        def f(x: int) -> int:
            """Parameter not mentioned
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="x",
                line=2,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_multiple_missing_parameter(self):
        """Test the checker on a function with multiple missing parameters"""
        src = '''
                def f(x: int, y: int) -> int:
                    """Both parameters not mentioned
                    """
                    pass
                '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="x",
                line=1,
            ),
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[1],
                args="y",
                line=1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_missing_parameter_with_period(self) -> None:
        """Test the checker on a function with no missing parameters,
        however there exist a period at the end of the parameter name"""
        src = '''
                def f(x: int) -> int:
                    """Return one plus x.
                    """
                    pass
                '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_no_missing_parameter_with_comma(self) -> None:
        """Test the checker on a function with no missing parameters,
        however there exist a period at the end of the parameter name"""
        src = '''
                def f(x: int) -> int:
                    """Return one plus x,
                    """
                    pass
                '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_missing_parameter_in_doctest(self) -> None:
        """Test the checker on a function with a missing parameter in the doctest"""
        src = '''
        def f(x: int) -> list:
            """Does not include parameter

            >>> f(1)
            [x for x in range(10)]
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="x",
                line=1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_missing_parameter_after_doctest(self) -> None:
        """Test the checker on a function with a missing parameter in the doctest"""
        src = '''
        def f(x: int) -> list:
            """Does not include parameter here

            >>> f(1)
            [x for x in range(10)]

            But I named x here
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_missing_parameter_in_multiple_doctest(self) -> None:
        """Test the checker on a function with a missing parameter in multiple doctests"""
        src = '''
        def f(x: int) -> list:
            """Does not include parameter

            >>> f(1)
            [1]
            >>> f(2)
            [x for x in range(2)]
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="x",
                line=1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_parameters(self) -> None:
        """Test the checker on a function with no parameters"""
        src = '''
        def f() -> list:
            """No parameters
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_empty_docstring(self) -> None:
        """Test the checker on a function with an empty docstring"""
        src = '''
        def f(x: int) -> list:
            """
            """
            pass
        '''
        mod = astroid.parse(src)

        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="x",
                line=1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_docstring(self) -> None:
        """Test the checker on a function with no docstring"""
        src = """
                def f(x: int) -> list:
                    pass
                """
        mod = astroid.parse(src)

        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="x",
                line=1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_docstring_no_parameters(self) -> None:
        """Test the checker on a function with no docstring and no parameters"""
        src = """
        def f() -> list:
            pass
        """
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_optional_parameter(self) -> None:
        """Test the checker on a function with an optional parameter."""
        src = '''
        def f(x: int, y: int = 5) -> int:
            """Return x plus y

            >>> f(1)
            6
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_missing_optional_parameter(self) -> None:
        """Test the checker on a function with a missing optional parameter."""
        src = '''
        def f(x: int, y: int = 5) -> int:
            """Return x plus something"""
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[1],
                args="y",
                line=1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)

    def test_no_missing_parameter_with_tabs(self) -> None:
        """Test the checker on a function where parameters in the docstring are separated by tabs."""
        src = '''
        def f(x: int, y: int) -> int:
            """I separat the parameters with tabs
            x\ty
            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_parameter_with_underscore(self) -> None:
        """Test the checker on a function with a parameter that contains underscores."""
        src = '''
        def f(param_name: int) -> None:
            """Process the param_name.

            """
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(function_node)

    def test_missing_parameter_with_underscore(self) -> None:
        """Test the checker on a function where a parameter with an underscore is not mentioned."""
        src = '''
        def f(param_name: int) -> None:
            """Does not mention the paramname."""
            pass
        '''
        mod = astroid.parse(src)
        function_node, *_ = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unmentioned-parameter",
                node=function_node.args.args[0],
                args="param_name",
                line=2,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(function_node)
