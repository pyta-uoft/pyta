import pylint.testutils
from astroid import nodes, parse

from python_ta.checkers.contract_checker import ContractChecker


class TestContractCheckerPreconditions(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ContractChecker

    def test_invalid_operator(self) -> None:
        """Test that !== operator is caught as invalid syntax."""
        src = """
        def f(x: int) -> float:
            '''Return 1/x.

            Preconditions:
                - x !== 0
            '''
            return 1 / x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("x !== 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_assignment_statement(self) -> None:
        """Test that assignment statements are caught as invalid precondition syntax."""
        src = """
        def f(x: int, word: str) -> int:
            '''Return the word duplicated x times.

            Preconditions:
                - x = 5
                - word = "hello"
            '''
            return x*word
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("x = 5",),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=('word = "hello"',),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_incorrect_whitespace(self) -> None:
        """Test that incorrect whitespaces get flagged as bad syntax."""
        src = """
        def f(x: int) -> int:
            '''Return x**2

            Preconditions:
                - 0 < = x < 10
            '''
            return x**2
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("0 < = x < 10",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_parenthesis(self):
        """Test that missing parenthesis are caught."""
        src = """
        def f(items: list) -> int:
            '''Return array length

            Preconditions:
                - len(items > 0
            '''
            return len(items)
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("len(items > 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_valid_preconditions(self) -> None:
        """Test that single-line preconditions with correct syntax pass."""
        src = """
        def f(x: int) -> int:
            '''Return 1/x

            Preconditions:
                - 1 <= x < 10
                - x == 5
                - x != 15
            '''
            return 1/x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_valid_multi_line_preconditions(self) -> None:
        """Test that multi-line preconditions with valid syntax pass."""
        src = """
        def f(data: list, threshold: int) -> int:
            '''Return list length of a positive integer array

            Preconditions:
                - len(data) > 0 and \
                  all(isinstance(x, int) for x in data) and \
                  threshold >= 0
                - data != []
            '''
            return len(data)
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_invalid_multi_line_preconditions(self) -> None:
        """Test that multi-line preconditions with invalid syntax are flagged."""
        src = """
        def f(data: list, threshold: int) -> int:
            '''Return list length of a positive integer array

            Preconditions:
                - len(data) > 0 and \
                  all(isinstance(x, int) for x in data) and \
                  threshold > = 0
                - data !== []
            '''
            return len(data)
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=(
                    "len(data) > 0 and all(isinstance(x, int) for x in data) and threshold > = 0",
                ),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("data !== []",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)


class TestContractCheckerPostconditions(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ContractChecker

    def test_invalid_postcondition_syntax(self) -> None:
        """Test that the same invalid syntaxes as the precondition checks are caught in the postcondition ones.
        Includes invalid !== operator, incorrect white space and assignment statements"""
        src = """
        def f(x: int) -> float:
            '''Return 1/x.

            Postconditions:
                - x !== 0
                - 0 < x < = 10
                - x = 5
            '''
            return 1 / x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-postcondition-syntax",
                node=func_node,
                args=("x !== 0",),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-postcondition-syntax",
                node=func_node,
                args=("0 < x < = 10",),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-postcondition-syntax",
                node=func_node,
                args=("x = 5",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_valid_postconditions(self) -> None:
        """Test that single-line postconditions with correct syntax pass."""
        src = """
        def f(x: int) -> int:
            '''Return 1/x

            Postconditions:
                - 1 <= x < 10
                - x == 5
                - x != 15
            '''
            return 1/x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_valid_return_value_syntax(self) -> None:
        """Test that valid postconditions using the return value identifier are not flagged."""
        src = """
        def f(x: int) -> list[int]:
            '''Return a list of length x containing all ones

            Postconditions:
                - $return_value[0] > 0 and $return_value[0] < 100
                - all(num >= 0 for num in $return_value)
            '''
            return [1]*x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_invalid_return_value_syntax(self) -> None:
        """Test that invalid postconditions using the return value identifier are flagged."""
        src = """
        def f(x: int) -> list[int]:
            '''Return a list of length x containing all ones

            Postconditions:
                - $return_value[0] > = 0
                - all(num >= 0 for num in $return_value
            '''
            return [1]*x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-postcondition-syntax",
                node=func_node,
                args=("$return_value[0] > = 0",),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-postcondition-syntax",
                node=func_node,
                args=("all(num >= 0 for num in $return_value",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_valid_multi_line_postconditions(self) -> None:
        """Test that valid multi-line postconditions with the return value identifier are not flagged."""
        src = """
        def f(x: int) -> list[int]:
            '''Return a list of length x containing all ones

            Postconditions:
                - $return_value[0] > 0 and \
                $return_value[0] < 100 and \
                $return_value[0] % 2 == 1
                - all(num >= 0 for num in $return_value)
            '''
            return [1]*x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)


class TestContractCheckerRepresentationInvariants(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ContractChecker

    def test_invalid_operator(self) -> None:
        """Test that !== is caught as invalid representation invariant syntax."""
        src = '''
        class Person:
            """A class representing a person.

            Representation Invariants:
                - self.age !== 0
            """
            age: int

            def __init__(self, age: int) -> None:
                self.age = age
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=("self.age !== 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_node)

    def test_assignment_statement(self) -> None:
        """Test that assignment statements are caught as invalid representation invariant syntax."""
        src = '''
        class Person:
            """A class representing a person.

            Representation Invariants:
                - self.age = 5
                - self.name = "hello"
            """
            age: int
            name: str

            def __init__(self, age: int, name: str) -> None:
                self.age = age
                self.name = name
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=("self.age = 5",),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=('self.name = "hello"',),
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_node)

    def test_incorrect_whitespace(self) -> None:
        """Test that incorrect whitespaces get flagged as bad representation invariant syntax."""
        src = '''
        class A:
            """A class.

            Representation Invariants:
                - 0 < = self.x < 10
            """
            x: int

            def __init__(self, x: int) -> None:
                self.x = x
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=("0 < = self.x < 10",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_node)

    def test_missing_parenthesis(self) -> None:
        """Test that missing parentheses are caught in representation invariants."""
        src = '''
        class Container:
            """A container class.

            Representation Invariants:
                - len(self.items > 0
            """
            items: list

            def __init__(self, items: list) -> None:
                self.items = items
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=("len(self.items > 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_node)

    def test_valid_representation_invariants(self) -> None:
        """Test that single-line representation invariants with correct syntax pass."""
        src = '''
        class Person:
            """A class representing a person.

            Representation Invariants:
                - self.name.isalpha()
                - self.age >= 0
                - self.age != 15
            """
            age: int
            name: str

            def __init__(self, name: str, age: int) -> None:
                self.name = name
                self.age = age
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertNoMessages():
            self.checker.visit_classdef(class_node)

    def test_valid_multi_line_representation_invariants(self) -> None:
        """Test that multi-line representation invariants with valid syntax pass."""
        src = '''
        class Data:
            """A data container.

            Representation Invariants:
                - len(self.items) > 0 and \
                  all(isinstance(x, int) for x in self.items) and \
                  self.threshold >= 0
                - self.items != []
            """
            items: list
            threshold: int

            def __init__(self, items: list, threshold: int) -> None:
                self.items = items
                self.threshold = threshold
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertNoMessages():
            self.checker.visit_classdef(class_node)

    def test_invalid_multi_line_representation_invariants(self) -> None:
        """Test that multi-line representation invariants with invalid syntax are flagged."""
        src = '''
        class Data:
            """A data container.

            Representation Invariants:
                - len(self.items) > 0 and \
                  all(isinstance(x, int) for x in self.items) and \
                  self.threshold > = 0
                - self.items !== []
            """
            items: list
            threshold: int

            def __init__(self, items: list, threshold: int) -> None:
                self.items = items
                self.threshold = threshold
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=(
                    "len(self.items) > 0 and all(isinstance(x, int) for x in self.items) and self.threshold > = 0",
                ),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=("self.items !== []",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_node)

    def test_class_without_docstring(self) -> None:
        """Test that a class without a docstring does not produce any messages."""
        src = """
        class Empty:
            x: int

            def __init__(self, x: int) -> None:
                self.x = x
        """

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertNoMessages():
            self.checker.visit_classdef(class_node)

    def test_class_without_representation_invariants(self) -> None:
        """Test that a class with a docstring but no representation invariants does not produce any messages."""
        src = '''
        class Simple:
            """A simple class without representation invariants."""
            x: int

            def __init__(self, x: int) -> None:
                self.x = x
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertNoMessages():
            self.checker.visit_classdef(class_node)

    def test_single_line_representation_invariant(self) -> None:
        """Test single-line form 'Representation Invariant: <cond>'."""
        src = '''
        class Counter:
            """A counter.

            Representation Invariant: self.count !== 0
            """
            count: int

            def __init__(self, count: int) -> None:
                self.count = count
        '''

        mod = parse(src)
        class_node, *_ = mod.nodes_of_class(nodes.ClassDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-representation-invariant-syntax",
                node=class_node,
                args=("self.count !== 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_classdef(class_node)
