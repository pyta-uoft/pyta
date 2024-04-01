"""
Test suite for the AccumulationTable class on different
types of accumulator loops
"""
import copy
import json
import os
import shutil
import subprocess
import sys

import pytest
import tabulate

from python_ta.debug import AccumulationTable
from python_ta.debug.snapshot import snapshot, snapshot_to_json


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


def test_accumulation_table_list_deepcopy():
    data = [[1], [2], [3]]
    with AccumulationTable(["data"]) as table:
        for sublist in data:
            sublist[0] *= 2
    recorded_value_0 = table.loop_accumulators["data"][0]
    expected_value_0 = [[1], [2], [3]]
    recorded_value_1 = table.loop_accumulators["data"][1]
    expected_value_1 = [[2], [2], [3]]
    recorded_value_2 = table.loop_accumulators["data"][2]
    expected_value_2 = [[2], [4], [3]]
    recorded_value_3 = table.loop_accumulators["data"][3]
    expected_value_3 = [[2], [4], [6]]
    assert recorded_value_0 == expected_value_0
    assert recorded_value_1 == expected_value_1
    assert recorded_value_2 == expected_value_2
    assert recorded_value_3 == expected_value_3


def test_loop_variables_with_deepcopy():
    data = [[[1, 2], [3, 4]], [[5, 6], [7, 8]], [[9, 10], [11, 12]]]

    with AccumulationTable(["data"]) as table:
        for nested_list in data:
            nested_list[0][0] += 100

    recorded_values = table.loop_variables["nested_list"]
    expected_values = ["N/A", [[101, 2], [3, 4]], [[105, 6], [7, 8]], [[109, 10], [11, 12]]]

    assert recorded_values == expected_values


def test_accumulation_table_dict_deepcopy():
    data = {"variable": [{"nested": 1}, {"nested": 2}]}

    with AccumulationTable(["data"]) as table:
        for item in data["variable"]:
            item["nested"] *= 2

    recorded_value_0 = table.loop_accumulators["data"][0]
    expected_value_0 = {"variable": [{"nested": 1}, {"nested": 2}]}
    recorded_value_1 = table.loop_accumulators["data"][1]
    expected_value_1 = {"variable": [{"nested": 2}, {"nested": 2}]}
    recorded_value_2 = table.loop_accumulators["data"][2]
    expected_value_2 = {"variable": [{"nested": 2}, {"nested": 4}]}
    assert recorded_value_0 == expected_value_0
    assert recorded_value_1 == expected_value_1
    assert recorded_value_2 == expected_value_2


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

    def check_accumulation_table_accumulator_deepcopy(self):
        if any(
            isinstance(sub, list)
            for sublist in self.items
            if isinstance(sublist, list)
            for sub in sublist
        ):
            return (
                "Checking only for lists with max depth 2, because if that works, other depths will work too."
                "Please provide list with max depth 2."
            )

        original_items = copy.deepcopy(self.items)
        with AccumulationTable(["self.items"]) as table:
            for sublist in self.items:
                if isinstance(sublist, list):
                    sublist[0] *= 2
        for i in range(0, len(table.loop_accumulators["self.items"])):
            recorded_value = table.loop_accumulators["self.items"][i]
            expected_value = []
            if i != 0:
                if isinstance(self.items[i - 1], list):
                    expected_value.extend(original_items[0 : i - 1])
                    expected_value.append(
                        [original_items[i - 1][0] * 2] + original_items[i - 1][1:]
                    )
                    expected_value.extend(original_items[i:])
                    original_items = expected_value
                else:
                    expected_value.extend(original_items)
            else:
                expected_value.extend(original_items)
            assert recorded_value == expected_value

    def check_accumulation_table_loop_variable_deepcopy(self):
        if any(
            isinstance(sub, list)
            for sublist in self.items
            if isinstance(sublist, list)
            for sub in sublist
        ):
            return (
                "Checking only for lists with max depth 2, because if that works, other depths will work too."
                "Please provide list with max depth 2."
            )

        original_items = copy.deepcopy(self.items)
        with AccumulationTable(["self.items"]) as table:
            for nested_list in self.items:
                if isinstance(nested_list, list):
                    nested_list[0] += 10
        recorded_values = table.loop_variables["nested_list"]
        expected_values = []
        for i in range(0, len(original_items) + 1):
            if i == 0:
                expected_values.append("N/A")
                continue
            if not isinstance(original_items[i - 1], list):
                expected_values.append(original_items[i - 1])
            else:
                expected_values.append([original_items[i - 1][0] + 10] + original_items[i - 1][1:])
        assert recorded_values == expected_values


def test_class_var() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.get_total()


def test_instance_var_accumulator() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.accumulate_instance_var()


def test_class_var_accumulator() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.accumulate_class_var()


def test_deepcopy_accumulator_in_class() -> None:
    checker = MyClass([1, 2, [3, 4], [5], 7, 8])
    checker.check_accumulation_table_accumulator_deepcopy()


def test_deepcopy_loop_variables_in_class() -> None:
    checker = MyClass([1, 2, [3, 4], [5], 7, 8])
    checker.check_accumulation_table_loop_variable_deepcopy()


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


def func_cyclic() -> list:
    """
    Function for snapshot_to_json() testing.
    """
    test_var = [1, 2, 3]
    test_var.append(test_var)
    return snapshot()


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


def test_snapshot_main_stackframe() -> None:
    """
    Assesses the accuracy of the snapshot() function in capturing global variables.
    Specifically, it verifies whether global variables (formatted as JSON) from another
    file within the same module ("snapshot_main_frame.py") are accurately captured.
    Subprocesses are utilized due to pytest's module configuration, where main is treated
    as a pytest module rather than the test file itself, causing global variables to be
    absent in the <module> stack frame. This behavior is inherent to pytest and cannot be modified.
    """
    current_directory = os.path.dirname(os.path.abspath(__file__))
    snapshot_main_frame_path = os.path.join(current_directory, "snapshot_main_frame.py")
    main_frame = subprocess.run(
        [sys.executable, snapshot_main_frame_path], capture_output=True, text=True
    )
    global_vars = main_frame.stdout
    parsed_global_vars = json.loads(global_vars)

    assert parsed_global_vars == {
        "__main__": {
            "team_lead": "David Liu",
            "SDS_projects": ["PyTA", "MarkUs", "Memory Models"],
            "team_num": 9,
        }
    }


def test_snapshot_to_json_primitive():
    """
    Test snapshot_to_json with snapshot data with only primitive data types.
    """
    snapshot_data = [
        {"func1": {"test_var1a": "David is cool!", "test_var2a": "DCS"}},
        {"__main__": {"num": 9, "is_david_cool": True, "num_alias": 9}},
    ]
    json_data = snapshot_to_json(snapshot_data)
    assert json_data == [
        {
            "isClass": True,
            "name": "func1",
            "id": None,
            "value": {"test_var1a": 1, "test_var2a": 2},
            "stack_frame": True,
        },
        {
            "isClass": True,
            "name": "__main__",
            "id": None,
            "value": {"num": 3, "is_david_cool": 4, "num_alias": 3},
            "stack_frame": True,
        },
        {"isClass": False, "name": "str", "id": 1, "value": "David is cool!"},
        {"isClass": False, "name": "str", "id": 2, "value": "DCS"},
        {"isClass": False, "name": "int", "id": 3, "value": 9},
        {"isClass": False, "name": "bool", "id": 4, "value": True},
    ]


def test_snapshot_to_json_lists_primitive_only():
    """
    Test snapshot_to_json data with lists including primitive data types.
    """
    snapshot_data = [
        {"func1": {"test_var1a": [1, 2, 3], "test_var2a": [True, False, True]}},
        {"__main__": {"projects": ["PyTA", "MarkUs", "Memory Models"]}},
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])

    assert json_data_frames == [
        {
            "id": None,
            "isClass": True,
            "name": "func1",
            "stack_frame": True,
            "value": {"test_var1a": 1, "test_var2a": 5},
        },
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"projects": 8},
        },
    ]

    assert json_data_objects == [
        {"id": 1, "isClass": False, "name": "list", "value": [2, 3, 4]},
        {"id": 2, "isClass": False, "name": "int", "value": 1},
        {"id": 3, "isClass": False, "name": "int", "value": 2},
        {"id": 4, "isClass": False, "name": "int", "value": 3},
        {"id": 5, "isClass": False, "name": "list", "value": [6, 7, 6]},
        {"id": 6, "isClass": False, "name": "bool", "value": True},
        {"id": 7, "isClass": False, "name": "bool", "value": False},
        {"id": 8, "isClass": False, "name": "list", "value": [9, 10, 11]},
        {"id": 9, "isClass": False, "name": "str", "value": "PyTA"},
        {"id": 10, "isClass": False, "name": "str", "value": "MarkUs"},
        {"id": 11, "isClass": False, "name": "str", "value": "Memory Models"},
    ]


def test_snapshot_to_json_tuples_primitive():
    """
    Test snapshot_to_json data with tuples including primitive data types.
    """
    snapshot_data = [
        {"func1": {"test_var1a": (1, 2, 3), "test_var2a": (True, False, True)}},
        {"__main__": {"projects": ("PyTA", "MarkUs", "Memory Models")}},
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])

    assert json_data_frames == [
        {
            "id": None,
            "isClass": True,
            "name": "func1",
            "stack_frame": True,
            "value": {"test_var1a": 1, "test_var2a": 5},
        },
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"projects": 8},
        },
    ]

    assert json_data_objects == [
        {"id": 1, "isClass": False, "name": "tuple", "value": [2, 3, 4]},
        {"id": 2, "isClass": False, "name": "int", "value": 1},
        {"id": 3, "isClass": False, "name": "int", "value": 2},
        {"id": 4, "isClass": False, "name": "int", "value": 3},
        {"id": 5, "isClass": False, "name": "tuple", "value": [6, 7, 6]},
        {"id": 6, "isClass": False, "name": "bool", "value": True},
        {"id": 7, "isClass": False, "name": "bool", "value": False},
        {"id": 8, "isClass": False, "name": "tuple", "value": [9, 10, 11]},
        {"id": 9, "isClass": False, "name": "str", "value": "PyTA"},
        {"id": 10, "isClass": False, "name": "str", "value": "MarkUs"},
        {"id": 11, "isClass": False, "name": "str", "value": "Memory Models"},
    ]


def test_snapshot_to_json_sets_primitive():
    """
    Test snapshot_to_json data with sets including primitive data types,
    using a dynamic approach to handle unordered set elements.
    """
    snapshot_data = [
        {"func1": {"test_var1a": {1, 2, 3}, "test_var2a": {True, False, True}}},
        {"__main__": {"projects": {"PyTA", "MarkUs", "Memory Models"}}},
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])

    expected_ids_for_test_var1a = [2, 3, 4]  # Assuming IDs are known or mocked
    expected_values_for_test_var1a = {1, 2, 3}

    expected_ids_for_test_var2a = [6, 7]  # True and False, assuming IDs
    expected_values_for_test_var2a = {True, False}

    expected_ids_for_projects = [9, 10, 11]  # Assuming IDs for project names
    expected_values_for_projects = {"MarkUs", "Memory Models", "PyTA"}

    assert json_data_frames == [
        {
            "id": None,
            "isClass": True,
            "name": "func1",
            "stack_frame": True,
            "value": {"test_var1a": 1, "test_var2a": 5},
        },
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"projects": 8},
        },
    ]

    # Validate that every id-value pair in the set matches an expected pair
    for id_, value in zip(expected_ids_for_test_var1a, expected_values_for_test_var1a):
        assert {"id": id_, "isClass": False, "name": "int", "value": value} in json_data_objects

    for id_, value in zip(expected_ids_for_test_var2a, expected_values_for_test_var2a):
        assert {"id": id_, "isClass": False, "name": "bool", "value": value} in json_data_objects

    for id_, value in zip(expected_ids_for_projects, expected_values_for_projects):
        assert {"id": id_, "isClass": False, "name": "str", "value": value} in json_data_objects


def test_snapshot_to_json_dicts_primitive():
    """
    Test snapshot_to_json data with dicts including primitive data types.
    """
    snapshot_data = [
        {"func1": {"var1": {"a": 1, "b": 2}}},
        {"__main__": {"var2": {"c": 3, "d": 4}}},
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])

    assert json_data_frames == [
        {"id": None, "isClass": True, "name": "func1", "stack_frame": True, "value": {"var1": 1}},
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"var2": 6},
        },
    ]
    assert json_data_objects == [
        {"id": 1, "isClass": False, "name": "dict", "value": {2: 3, 4: 5}},
        {"id": 2, "isClass": False, "name": "str", "value": "a"},
        {"id": 3, "isClass": False, "name": "int", "value": 1},
        {"id": 4, "isClass": False, "name": "str", "value": "b"},
        {"id": 5, "isClass": False, "name": "int", "value": 2},
        {"id": 6, "isClass": False, "name": "dict", "value": {7: 8, 9: 10}},
        {"id": 7, "isClass": False, "name": "str", "value": "c"},
        {"id": 8, "isClass": False, "name": "int", "value": 3},
        {"id": 9, "isClass": False, "name": "str", "value": "d"},
        {"id": 10, "isClass": False, "name": "int", "value": 4},
    ]


def test_snapshot_to_json_lists_of_dicts():
    """
    Test snapshot_to_json data with lists containing dictionaries.
    """
    snapshot_data = [
        {
            "func1": {
                "test_list1": [{"key1": 1}, {"key2": 2}],
                "test_list2": [{"key3": 3}, {"key4": 4}],
            }
        },
        {
            "__main__": {
                "projects": [
                    {"name": "Project1", "status": "active"},
                    {"name": "Project2", "status": "inactive"},
                ]
            }
        },
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])

    assert json_data_frames == [
        {
            "id": None,
            "isClass": True,
            "name": "func1",
            "stack_frame": True,
            "value": {"test_list1": 1, "test_list2": 8},
        },
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"projects": 15},
        },
    ]
    assert json_data_objects == [
        {"id": 1, "isClass": False, "name": "list", "value": [2, 5]},
        {"id": 2, "isClass": False, "name": "dict", "value": {3: 4}},
        {"id": 3, "isClass": False, "name": "str", "value": "key1"},
        {"id": 4, "isClass": False, "name": "int", "value": 1},
        {"id": 5, "isClass": False, "name": "dict", "value": {6: 7}},
        {"id": 6, "isClass": False, "name": "str", "value": "key2"},
        {"id": 7, "isClass": False, "name": "int", "value": 2},
        {"id": 8, "isClass": False, "name": "list", "value": [9, 12]},
        {"id": 9, "isClass": False, "name": "dict", "value": {10: 11}},
        {"id": 10, "isClass": False, "name": "str", "value": "key3"},
        {"id": 11, "isClass": False, "name": "int", "value": 3},
        {"id": 12, "isClass": False, "name": "dict", "value": {13: 14}},
        {"id": 13, "isClass": False, "name": "str", "value": "key4"},
        {"id": 14, "isClass": False, "name": "int", "value": 4},
        {"id": 15, "isClass": False, "name": "list", "value": [16, 21]},
        {"id": 16, "isClass": False, "name": "dict", "value": {17: 18, 19: 20}},
        {"id": 17, "isClass": False, "name": "str", "value": "name"},
        {"id": 18, "isClass": False, "name": "str", "value": "Project1"},
        {"id": 19, "isClass": False, "name": "str", "value": "status"},
        {"id": 20, "isClass": False, "name": "str", "value": "active"},
        {"id": 21, "isClass": False, "name": "dict", "value": {17: 22, 19: 23}},
        {"id": 22, "isClass": False, "name": "str", "value": "Project2"},
        {"id": 23, "isClass": False, "name": "str", "value": "inactive"},
    ]


def test_snapshot_to_json_dicts_of_lists():
    """
    Test snapshot_to_json data with dictionaries containing lists.
    """
    snapshot_data = [
        {"func1": {"var1": ["a", "b", "c"], "var2": [1, 2, 3]}},
        {"__main__": {"config": ["debug", "verbose", "production"], "values": [100, 200, 300]}},
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])
    assert json_data_frames == [
        {
            "id": None,
            "isClass": True,
            "name": "func1",
            "stack_frame": True,
            "value": {"var1": 1, "var2": 5},
        },
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"config": 9, "values": 13},
        },
    ]
    assert json_data_objects == [
        {"id": 1, "isClass": False, "name": "list", "value": [2, 3, 4]},
        {"id": 2, "isClass": False, "name": "str", "value": "a"},
        {"id": 3, "isClass": False, "name": "str", "value": "b"},
        {"id": 4, "isClass": False, "name": "str", "value": "c"},
        {"id": 5, "isClass": False, "name": "list", "value": [6, 7, 8]},
        {"id": 6, "isClass": False, "name": "int", "value": 1},
        {"id": 7, "isClass": False, "name": "int", "value": 2},
        {"id": 8, "isClass": False, "name": "int", "value": 3},
        {"id": 9, "isClass": False, "name": "list", "value": [10, 11, 12]},
        {"id": 10, "isClass": False, "name": "str", "value": "debug"},
        {"id": 11, "isClass": False, "name": "str", "value": "verbose"},
        {"id": 12, "isClass": False, "name": "str", "value": "production"},
        {"id": 13, "isClass": False, "name": "list", "value": [14, 15, 16]},
        {"id": 14, "isClass": False, "name": "int", "value": 100},
        {"id": 15, "isClass": False, "name": "int", "value": 200},
        {"id": 16, "isClass": False, "name": "int", "value": 300},
    ]


def test_snapshot_to_json_dicts_of_dicts():
    """
    Test snapshot_to_json data with dictionaries containing other dictionaries.
    """
    snapshot_data = [
        {"func1": {"nested1": {"inner1": 1, "inner2": 2}, "nested2": {"inner3": 3, "inner4": 4}}},
        {
            "__main__": {
                "configurations": {
                    "config1": {"settingA": "valueA", "settingB": "valueB"},
                    "config2": {"settingC": "valueC", "settingD": "valueD"},
                }
            }
        },
    ]

    json_data = snapshot_to_json(snapshot_data)
    json_data_frames = json_data[0:2]
    json_data_objects = sorted(json_data[2:], key=lambda x: x["id"])
    assert json_data_frames == [
        {
            "id": None,
            "isClass": True,
            "name": "func1",
            "stack_frame": True,
            "value": {"nested1": 1, "nested2": 6},
        },
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"configurations": 11},
        },
    ]
    assert json_data_objects == [
        {"id": 1, "isClass": False, "name": "dict", "value": {2: 3, 4: 5}},
        {"id": 2, "isClass": False, "name": "str", "value": "inner1"},
        {"id": 3, "isClass": False, "name": "int", "value": 1},
        {"id": 4, "isClass": False, "name": "str", "value": "inner2"},
        {"id": 5, "isClass": False, "name": "int", "value": 2},
        {"id": 6, "isClass": False, "name": "dict", "value": {7: 8, 9: 10}},
        {"id": 7, "isClass": False, "name": "str", "value": "inner3"},
        {"id": 8, "isClass": False, "name": "int", "value": 3},
        {"id": 9, "isClass": False, "name": "str", "value": "inner4"},
        {"id": 10, "isClass": False, "name": "int", "value": 4},
        {"id": 11, "isClass": False, "name": "dict", "value": {12: 13, 18: 19}},
        {"id": 12, "isClass": False, "name": "str", "value": "config1"},
        {"id": 13, "isClass": False, "name": "dict", "value": {14: 15, 16: 17}},
        {"id": 14, "isClass": False, "name": "str", "value": "settingA"},
        {"id": 15, "isClass": False, "name": "str", "value": "valueA"},
        {"id": 16, "isClass": False, "name": "str", "value": "settingB"},
        {"id": 17, "isClass": False, "name": "str", "value": "valueB"},
        {"id": 18, "isClass": False, "name": "str", "value": "config2"},
        {"id": 19, "isClass": False, "name": "dict", "value": {20: 21, 22: 23}},
        {"id": 20, "isClass": False, "name": "str", "value": "settingC"},
        {"id": 21, "isClass": False, "name": "str", "value": "valueC"},
        {"id": 22, "isClass": False, "name": "str", "value": "settingD"},
        {"id": 23, "isClass": False, "name": "str", "value": "valueD"},
    ]


def test_snapshot_to_json_user_defined_class_primitive():
    """
    Test snapshot_to_json with snapshot data including a user-defined class with primitive attributes,
    corrected to match the observed output ordering.
    """

    class MyClass:
        """
        Represents a simple class with two attributes initialized upon instantiation.

        Attributes:
            attr1 (str): A string attribute initialized to "value1".
            attr2 (int): An integer attribute initialized to 42.
        """

        def __init__(self):
            self.attr1 = "value1"
            self.attr2 = 42

    my_object = MyClass()

    snapshot_data = [
        {"__main__": {"my_object": my_object}},
    ]

    json_data = snapshot_to_json(snapshot_data)

    expected_output = [
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"my_object": 1},
        },
        {"id": 2, "isClass": False, "name": "str", "value": "value1"},
        {"id": 3, "isClass": False, "name": "int", "value": 42},
        {
            "id": 1,
            "isClass": True,
            "name": "MyClass",
            "value": {"attr1": 2, "attr2": 3},
        },
    ]

    assert json_data == expected_output


def test_snapshot_to_json_user_defined_class_nested():
    """
    Test snapshot_to_json with snapshot data including a user-defined class
    with nested user-defined class attributes, corrected to match the observed output ordering.
    """

    class NestedClass:
        """
        Represents a nested class with two attributes.

        Attributes:
            nested_attr1 (str): A string attribute initialized to "nested value".
            nested_attr2 (bool): A boolean attribute initialized to False.
        """

        def __init__(self):
            self.nested_attr1 = "nested value"
            self.nested_attr2 = False

    class MyClass:
        """
        Represents a class with an attribute that is an instance of another class
        and another primitive attribute.

        Attributes:
            attr1 (NestedClass): An instance of NestedClass as an attribute,
            demonstrating composition.
            attr2 (int): An integer attribute initialized to 99.
        """

        def __init__(self):
            self.attr1 = NestedClass()
            self.attr2 = 99

    my_object = MyClass()

    snapshot_data = [
        {"__main__": {"my_object": my_object}},
    ]

    json_data = snapshot_to_json(snapshot_data)

    expected_output = [
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"my_object": 1},
        },
        {"id": 3, "isClass": False, "name": "str", "value": "nested value"},
        {"id": 4, "isClass": False, "name": "bool", "value": False},
        {
            "id": 2,
            "isClass": True,
            "name": "NestedClass",
            "value": {"nested_attr1": 3, "nested_attr2": 4},
        },
        {"id": 5, "isClass": False, "name": "int", "value": 99},
        {
            "id": 1,
            "isClass": True,
            "name": "MyClass",
            "value": {"attr1": 2, "attr2": 5},
        },
    ]

    assert json_data == expected_output


def test_output_to_existing_file(tmp_path) -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    output_file = tmp_path / "output.txt"
    with open(output_file, "a") as file:
        file.write("Existing Content")
        file.write("\n")
    with AccumulationTable(["sum_so_far"], output=str(output_file)) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number
        iteration_dict = table._create_iteration_dict()

    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}

    with open(output_file, "r") as file:
        content = file.read()
        expected_values = tabulate.tabulate(
            iteration_dict,
            headers="keys",
            colalign=(*["left"] * len(iteration_dict),),
            disable_numparse=True,
            missingval="None",
        )
    assert "Existing Content" in content
    assert expected_values in content

    shutil.rmtree(tmp_path)


def test_output_to_new_file(tmp_path) -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["sum_so_far"], output=str(tmp_path / "output.txt")) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number
        iteration_dict = table._create_iteration_dict()

    output_file = tmp_path / "output.txt"
    assert output_file.exists()
    assert table.loop_variables == {"number": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}

    with open(output_file, "r") as file:
        content = file.read()
        expected_values = tabulate.tabulate(
            iteration_dict,
            headers="keys",
            colalign=(*["left"] * len(iteration_dict),),
            disable_numparse=True,
            missingval="None",
        )
    assert expected_values in content

    shutil.rmtree(tmp_path)
