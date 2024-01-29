"""
Test suite for the AccumulationTable class on different
types of accumulator loops
"""
import copy
import shutil

import pytest
import tabulate

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


# The functions (and top-level variables) below are for snapshot() testing purposes ONLY
team_lead = "David Liu"
SDS_projects = ["PyTA", "MarkUs", "Memory Models"]
team_num = 9


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
        "__main__": {
            "team_lead": "David Liu",
            "SDS_projects": ["PyTA", "MarkUs", "Memory Models"],
            "team_num": 9,
        }
    } == local_vars[0]

    assert {
        "func1": {"test_var2a": "Students Developing Software", "test_var1a": "David is cool!"}
    } == local_vars[1]


def test_snapshot_two_levels() -> None:
    """
    Evaluates the precision of the snapshot() function in capturing
    local variables during a two-level nested function call.
    """
    local_vars = func2()
    print(local_vars)

    assert {
        "__main__": {
            "team_lead": "David Liu",
            "SDS_projects": ["PyTA", "MarkUs", "Memory Models"],
            "team_num": 9,
        }
    } == local_vars[1]

    assert {
        "func1": {"test_var2a": "Students Developing Software", "test_var1a": "David is cool!"}
    } == local_vars[0]

    assert {
        "func2": {
            "test_var1b": {"SDS_coolest_project": "PyTA"},
            "test_var2b": ("Aina", "Merrick", "Varun", "Utku"),
        }
    } == local_vars[2]


def test_snapshot_three_levels() -> None:
    """
    Evaluates the precision of the snapshot() function in capturing
    local variables during a three-level nested function call.
    """
    local_vars = func3()

    assert {
        "__main__": {
            "team_lead": "David Liu",
            "SDS_projects": ["PyTA", "MarkUs", "Memory Models"],
            "team_num": 9,
        }
    } == local_vars[1]

    assert {
        "func1": {"test_var2a": "Students Developing Software", "test_var1a": "David is cool!"}
    } == local_vars[0]

    assert {
        "func2": {
            "test_var1b": {"SDS_coolest_project": "PyTA"},
            "test_var2b": ("Aina", "Merrick", "Varun", "Utku"),
        }
    } == local_vars[2]

    assert {"func3": {"i": 4, "test_var1c": [0, 1, 2, 3, 4]}} == local_vars[3]


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
