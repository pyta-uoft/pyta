"""
Test suite for the AccumulationTable class on different
types of accumulator loops
"""

import pytest

from python_ta.debug import AccumulationTable
from python_ta.debug.snapshot import snapshot


def test_one_accumulator() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["sum_so_far"]) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number

    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}


def test_one_accumulator_while_loop() -> None:
    number = 10
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["number", "sum_so_far"]) as table:
        while number in test_list:
            sum_so_far = sum_so_far + number
            number += 10

    assert table.loop_accumulators == {"number": [10, 20, 30, 40], "sum_so_far": [0, 10, 30, 60]}


def test_two_accumulator_while_loop() -> None:
    number = 10
    test_list = [10, 20, 30]
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["number", "sum_so_far", "list_so_far"]) as table:
        while number in test_list:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]
            number += 10

    assert table.loop_accumulators == {
        "number": [10, 20, 30, 40],
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


def test_two_accumulators() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["sum_so_far", "list_so_far"]) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]

    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


def test_empty_accumulators_and_variables() -> None:
    with pytest.raises(AssertionError):
        number = 10
        test_list = [10, 20, 30]
        sum_so_far = 0
        with AccumulationTable([]) as table:
            while number in test_list:
                sum_so_far = sum_so_far + number
                number += 10


def test_three_different_loop_lineno() -> None:
    test_list = [10, 20, 30]
    list_so_far = []
    with AccumulationTable(["sum_so_far", "list_so_far"]) as table:
        sum_so_far = 0
        for number in test_list:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]
    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


def test_four_different_loop_lineno() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["sum_so_far", "list_so_far"]) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]
        b = ""
    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


def test_five_nested_for_loop() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["sum_so_far", "list_so_far"]) as table:
        i = 0
        if True:
            for number in test_list:
                sum_so_far = sum_so_far + number
                list_so_far = list_so_far + [number]
        while i < 5:
            i += 1
    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


def test_five_nested_while_loop() -> None:
    number = 10
    test_list = [10, 20, 30]
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["number", "sum_so_far", "list_so_far"]) as table:
        if True:
            while number in test_list:
                sum_so_far = sum_so_far + number
                list_so_far = list_so_far + [number]
                number += 10
        for number in test_list:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]

    assert table.loop_accumulators == {
        "number": [10, 20, 30, 40],
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


class MyClass:
    items: list
    sum_so_far: int
    difference_so_far = 0

    def __init__(self, items: list):
        self.items = items
        self.sum_so_far = 0

    def get_total(self) -> None:
        sum_so_far = 0
        with AccumulationTable(["sum_so_far"]) as table:
            for item in self.items:
                sum_so_far = sum_so_far + item

        assert table.loop_variables == {"item": ["N/A", 10, 20, 30]}
        assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}

    def accumulate_instance_var(self) -> None:
        with AccumulationTable(["self.sum_so_far"]) as table:
            for item in self.items:
                self.sum_so_far = self.sum_so_far + item

        assert table.loop_variables == {"item": ["N/A", 10, 20, 30]}
        assert table.loop_accumulators == {"self.sum_so_far": [0, 10, 30, 60]}

    def accumulate_class_var(self) -> None:
        with AccumulationTable(["MyClass.difference_so_far"]) as table:
            for item in self.items:
                MyClass.difference_so_far = MyClass.difference_so_far - item

        assert table.loop_variables == {"item": ["N/A", 10, 20, 30]}
        assert table.loop_accumulators == {"MyClass.difference_so_far": [0, -10, -30, -60]}


def test_class_var() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.get_total()


def test_instance_var_accumulator() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.accumulate_instance_var()


def test_class_var_accumulator() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.accumulate_class_var()


def test_expression_accumulator() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["sum_so_far * 2"]) as table:
        for item in test_list:
            sum_so_far = sum_so_far + item

    assert table.loop_variables == {"item": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {"sum_so_far * 2": [0, 20, 60, 120]}


def test_invalid_accumulator() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with pytest.raises(NameError):
        with AccumulationTable(["invalid"]) as table:
            for number in test_list:
                sum_so_far = sum_so_far + number


def test_two_loop_vars_one_accumulator() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["sum_so_far"]) as table:
        for index, item in enumerate(test_list):
            sum_so_far = sum_so_far + item

    assert table.loop_variables == {"index": ["N/A", 0, 1, 2], "item": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}


def test_two_loop_vars_two_accumulators() -> None:
    test_dict = {1: "I lo", 2: "ve CS", 3: "C110"}
    keys_so_far = 0
    values_so_far = ""
    with AccumulationTable(["keys_so_far", "values_so_far"]) as table:
        for key, value in test_dict.items():
            keys_so_far = keys_so_far + key
            values_so_far = values_so_far + value

    assert table.loop_variables == {
        "key": ["N/A", 1, 2, 3],
        "value": ["N/A", "I lo", "ve CS", "C110"],
    }
    assert table.loop_accumulators == {
        "keys_so_far": [0, 1, 3, 6],
        "values_so_far": ["", "I lo", "I love CS", "I love CSC110"],
    }


def test_loop_variable_initialized_in_loop() -> None:
    with AccumulationTable(["i"]) as table:
        for number in [10, 20, 30, 40, 50, 60]:
            i = number

    assert table.loop_variables == {"number": ["N/A", 10, 20, 30, 40, 50, 60]}
    assert table.loop_accumulators == {"i": ["N/A", 10, 20, 30, 40, 50, 60]}


def test_loop_variable_conditionally_initialized_in_loop() -> None:
    with AccumulationTable(["i"]) as table:
        for number in [10, 20, 30, 40, 50, 60]:
            if number == 30:
                i = number

    assert table.loop_variables == {"number": ["N/A", 10, 20, 30, 40, 50, 60]}
    assert table.loop_accumulators == {"i": ["N/A", "N/A", "N/A", 30, 30, 30, 30]}


def test_uninitialized_loop_accumulators() -> None:
    with pytest.raises(NameError):
        with AccumulationTable(["i"]) as table:
            for number in [10, 20, 30, 40, 50, 60]:
                _ = number


# The functions below are for snapshot() testing purposes ONLY
def func1() -> list:
    """
    Function for snapshot() testing.
    """
    test_var1a = "David is cool!"
    test_var2a = "Students Developing Software"
    return snapshot()


def func2() -> list:
    """
    Function for snapshot() testing.
    """
    test_var1b = {"SDS_coolest_project": "PyTA"}
    test_var2b = ("Aina", "Merrick", "Varun", "Utku")
    return func1()


def func3() -> list:
    """
    Function for snapshot() testing.
    """
    test_var1c = []
    for i in range(5):
        test_var1c.append(i)

    return func2()


def test_snapshot_one_level() -> None:
    """
    Examines whether the snapshot() function accurately captures
    the local variables of a singular function call,
    devoid of any nested levels.
    """
    local_vars = func1()

    assert {
        "func1": {"test_var2a": "Students Developing Software", "test_var1a": "David is cool!"}
    } == local_vars[0]


def test_snapshot_two_levels() -> None:
    """
    Evaluates the precision of the snapshot() function in capturing
    local variables during a two-level nested function call.
    """
    local_vars = func2()

    assert {
        "func1": {"test_var2a": "Students Developing Software", "test_var1a": "David is cool!"}
    } == local_vars[0]
    assert {
        "func2": {
            "test_var1b": {"SDS_coolest_project": "PyTA"},
            "test_var2b": ("Aina", "Merrick", "Varun", "Utku"),
        }
    } == local_vars[1]


def test_snapshot_three_levels() -> None:
    """
    Evaluates the precision of the snapshot() function in capturing
    local variables during a three-level nested function call.
    """

    local_vars = func3()

    assert {
        "func1": {"test_var2a": "Students Developing Software", "test_var1a": "David is cool!"}
    } == local_vars[0]
    assert {
        "func2": {
            "test_var1b": {"SDS_coolest_project": "PyTA"},
            "test_var2b": ("Aina", "Merrick", "Varun", "Utku"),
        }
    } == local_vars[1]
    assert {"func3": {"i": 4, "test_var1c": [0, 1, 2, 3, 4]}} == local_vars[2]
