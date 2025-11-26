"""
Test suite for the AccumulationTable class on different
types of accumulator loops
"""

import copy
import csv
import io
import shutil
import sys

import pytest
import tabulate

from python_ta.debug import AccumulationTable


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

    assert table.loop_accumulators == {
        "number": [10, 20, 30, 40],
        "sum_so_far": [0, 10, 30, 60],
    }


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
    assert table.loops[0]["loop_variables"] == {"number": ["N/A", 10, 20, 30]}
    assert table.loops[0]["loop_accumulators"] == {
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

    assert table.loops[0]["loop_accumulators"] == {
        "number": [10, 20, 30, 40],
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }


def test_accumulation_table_nested_tuple():
    data = [
        ("a", ([1, 2], 3)),
        ("b", ([4, 5], 6)),
        ("c", ([7, 8], 9)),
    ]

    with AccumulationTable(["data"]) as table:
        for letter, (lst, num) in data:
            lst[0] *= 2

    assert table.loop_variables == {
        "letter": ["N/A", "a", "b", "c"],
        "lst": ["N/A", [2, 2], [8, 5], [14, 8]],
        "num": ["N/A", 3, 6, 9],
    }


def test_accumulation_table_deeply_nested_tuple():
    data = [
        ("x", ([1], (2, 3))),
        ("y", ([4], (5, 6))),
    ]

    with AccumulationTable(["data"]) as table:
        for a, (b, (c, d)) in data:
            b[0] += 1

    assert table.loop_variables["a"] == ["N/A", "x", "y"]
    assert table.loop_variables["b"] == ["N/A", [2], [5]]
    assert table.loop_variables["c"] == ["N/A", 2, 5]
    assert table.loop_variables["d"] == ["N/A", 3, 6]


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


@pytest.mark.skipif(sys.version_info < (3, 10), reason="requires Python 3.10 or higher")
def test_expression_with_loop_var_accumulator() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["item * 2"]) as table:
        for item in test_list:
            sum_so_far = sum_so_far + item

    assert table.loop_variables == {"item": ["N/A", 10, 20, 30]}
    assert table.loop_accumulators == {"item * 2": ["N/A", 20, 40, 60]}


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


@pytest.fixture(params=["table", "csv"])
def output_format(request):
    """Parametrized fixture for output format."""
    return request.param


@pytest.fixture
def existing_file_content(tmp_path):
    """Fixture that creates a file with existing content."""
    output_file = tmp_path / "output.txt"
    with open(output_file, "a") as file:
        file.write("Existing Content")
        file.write("\n")
    return output_file


def get_expected_content(format_type):
    """Return the exact expected file content as literal strings."""
    if format_type == "csv":
        return """iteration,number,sum_so_far,avg_so_far,list_so_far
0,N/A,0,,[]
1,10,10,10.0,"[(10, 10.0)]"
2,20,30,15.0,"[(10, 10.0), (30, 15.0)]"
3,30,60,20.0,"[(10, 10.0), (30, 15.0), (60, 20.0)]"
4,40,100,25.0,"[(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0)]"
5,50,150,30.0,"[(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0)]"
6,60,210,35.0,"[(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0), (210, 35.0)]"
"""
    else:
        return """iteration    number    sum_so_far    avg_so_far    list_so_far
-----------  --------  ------------  ------------  ---------------------------------------------------------------------------
0            N/A       0             None          []
1            10        10            10.0          [(10, 10.0)]
2            20        30            15.0          [(10, 10.0), (30, 15.0)]
3            30        60            20.0          [(10, 10.0), (30, 15.0), (60, 20.0)]
4            40        100           25.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0)]
5            50        150           30.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0)]
6            60        210           35.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0), (210, 35.0)]"""


def test_output_to_existing_file(existing_file_content, output_format):
    """Test output to existing file with parametrized format."""
    numbers = [10, 20, 30, 40, 50, 60]
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None

    table_kwargs = {"output": str(existing_file_content)}
    if output_format == "csv":
        table_kwargs["format"] = "csv"

    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"], **table_kwargs):
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    with open(existing_file_content, "r") as file:
        content = file.read()

    expected_table_content = get_expected_content(output_format)
    if output_format == "table":
        expected_file_content = "Existing Content\n" + expected_table_content + "\n"
    else:
        expected_file_content = "Existing Content\n" + expected_table_content

    assert content == expected_file_content


def test_output_to_new_file(tmp_path, output_format):
    """Test output to new file with parametrized format."""
    output_file = tmp_path / "output.txt"
    numbers = [10, 20, 30, 40, 50, 60]
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None

    table_kwargs = {"output": str(output_file)}
    if output_format == "csv":
        table_kwargs["format"] = "csv"

    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"], **table_kwargs):
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    with open(output_file, "r") as file:
        content = file.read()

    expected_content = get_expected_content(output_format)
    if output_format == "table":
        expected_content = expected_content + "\n"

    assert content == expected_content


def test_three_sequential_loops() -> None:
    """Test tracking accumulators across three sequential loops (for, for, while)"""
    test_list = [10, 20, 30]
    sum_so_far = 0
    i = 0
    with AccumulationTable(["sum_so_far", "i"]) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number
        for j in range(len(test_list)):
            sum_so_far += 1
        while i < 10:
            i += 1
            sum_so_far -= i

    # First loop
    assert table.loops[0]["loop_variables"] == {"number": ["N/A", 10, 20, 30]}
    assert table.loops[0]["loop_accumulators"] == {
        "sum_so_far": [0, 10, 30, 60],
        "i": [0, 0, 0, 0],
    }

    # Second loop
    assert table.loops[1]["loop_variables"] == {"j": ["N/A", 0, 1, 2]}
    assert table.loops[1]["loop_accumulators"] == {
        "sum_so_far": [60, 61, 62, 63],
        "i": [0, 0, 0, 0],
    }

    # Third loop
    assert table.loops[2]["loop_variables"] == {}
    assert table.loops[2]["loop_accumulators"] == {
        "sum_so_far": [63, 62, 60, 57, 53, 48, 42, 35, 27, 18, 8],
        "i": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    }


def test_two_for_loops_different_accumulators() -> None:
    """Test two for loops tracking different accumulators"""
    numbers = [1, 2, 3]
    letters = ["a", "b", "c"]
    sum_nums = 0
    concat_letters = ""

    with AccumulationTable(["sum_nums", "concat_letters"]) as table:
        for num in numbers:
            sum_nums += num
        for letter in letters:
            concat_letters += letter

    # First loop
    assert table.loops[0]["loop_variables"] == {"num": ["N/A", 1, 2, 3]}
    assert table.loops[0]["loop_accumulators"] == {
        "sum_nums": [0, 1, 3, 6],
        "concat_letters": ["", "", "", ""],
    }

    # Second loop
    assert table.loops[1]["loop_variables"] == {"letter": ["N/A", "a", "b", "c"]}
    assert table.loops[1]["loop_accumulators"] == {
        "sum_nums": [6, 6, 6, 6],
        "concat_letters": ["", "a", "ab", "abc"],
    }


def test_multiple_loops_with_shared_accumulator() -> None:
    """Test multiple loops all modifying the same accumulator"""
    total = 0

    with AccumulationTable(["total"]) as table:
        for x in [10, 20]:
            total += x
        for y in [5, 15]:
            total += y
        for z in [100]:
            total += z

    # First loop
    assert table.loops[0]["loop_variables"] == {"x": ["N/A", 10, 20]}
    assert table.loops[0]["loop_accumulators"] == {"total": [0, 10, 30]}

    # Second loop
    assert table.loops[1]["loop_variables"] == {"y": ["N/A", 5, 15]}
    assert table.loops[1]["loop_accumulators"] == {"total": [30, 35, 50]}

    # Third loop
    assert table.loops[2]["loop_variables"] == {"z": ["N/A", 100]}
    assert table.loops[2]["loop_accumulators"] == {"total": [50, 150]}


def test_while_and_for_loops_mixed() -> None:
    """Test mixing while and for loops"""
    counter = 0
    items = []

    with AccumulationTable(["counter", "items"]) as table:
        while counter < 3:
            counter += 1
        for item in ["x", "y"]:
            items.append(item)

    # First loop
    assert table.loops[0]["loop_variables"] == {}
    assert table.loops[0]["loop_accumulators"] == {
        "counter": [0, 1, 2, 3],
        "items": [[], [], [], []],
    }

    # Second loop
    assert table.loops[1]["loop_variables"] == {"item": ["N/A", "x", "y"]}
    assert table.loops[1]["loop_accumulators"] == {
        "counter": [3, 3, 3],
        "items": [[], ["x"], ["x", "y"]],
    }


def test_two_loops_with_list_accumulator() -> None:
    """Test two loops both appending to same list accumulator"""
    combined = []

    with AccumulationTable(["combined"]) as table:
        for num in [1, 2]:
            combined.append(num)
        for letter in ["a", "b"]:
            combined.append(letter)

    # First loop
    assert table.loops[0]["loop_variables"] == {"num": ["N/A", 1, 2]}
    assert table.loops[0]["loop_accumulators"] == {"combined": [[], [1], [1, 2]]}

    # Second loop
    assert table.loops[1]["loop_variables"] == {"letter": ["N/A", "a", "b"]}
    assert table.loops[1]["loop_accumulators"] == {
        "combined": [[1, 2], [1, 2, "a"], [1, 2, "a", "b"]]
    }


def test_multiple_loops_no_accumulators() -> None:
    """Test multiple loops with only loop variables tracked (no accumulators specified)"""
    with AccumulationTable([]) as table:
        for x in [1, 2]:
            pass
        for y in [3, 4]:
            pass

    # Should track loop variables even without accumulators
    assert table.loops[0]["loop_variables"] == {"x": ["N/A", 1, 2]}
    assert table.loops[0]["loop_accumulators"] == {}

    assert table.loops[1]["loop_variables"] == {"y": ["N/A", 3, 4]}
    assert table.loops[1]["loop_accumulators"] == {}


def test_nested_not_tracked_for_loops() -> None:
    """Test nested for loops to see if only outermost loop is tracked"""
    with AccumulationTable([]) as table:
        for x in [1, 2]:
            for y in [3, 4]:
                pass

    # Following attributes shouldn't be None since there is only one tracked loop
    assert table.loop_accumulators is not None and table.loop_variables is not None


def test_nested_not_tracked_while_loops() -> None:
    """Test nested while loops to see if only outermost loop is tracked"""
    x = 0
    y = 0
    with AccumulationTable(["x", "y"]) as table:
        while x < 10:
            while y < 20:
                y += 1
            y -= x
            x += 2

    # Following attributes shouldn't be None since there is only one tracked loop
    assert table.loop_accumulators is not None and table.loop_variables is not None


def test_nested_not_tracked_mixed_loops() -> None:
    """Test nested mixed loops to see if only outermost loop is tracked"""
    x = 0
    with AccumulationTable(["x"]) as table:
        while x < 10:
            for y in range(20):
                pass
            x += 2

    # Following attributes shouldn't be None since there is only one tracked loop
    assert table.loop_accumulators is not None and table.loop_variables is not None
    assert "y" not in table.loop_accumulators

    y = 0
    with AccumulationTable([]) as table:
        for x in range(10):
            while y < 10:
                y += 1
            x += 2

    # Following attributes shouldn't be None since there is only one tracked loop
    assert table.loop_accumulators is not None and table.loop_variables is not None
    assert "y" not in table.loop_accumulators


def test_nested_not_tracked_multiple_loops() -> None:
    """Test multiple nested mixed loops to see if only outermost loop is tracked"""
    with AccumulationTable([]) as table:
        for x in range(10):
            for y in range(10):
                for z in range(10):
                    pass

    # Following attributes shouldn't be None since there is only one tracked loop
    assert table.loop_accumulators is not None and table.loop_variables is not None
    assert all(elem not in ["y", "z"] for elem in table.loop_variables)


def test_per_loop_accumulators_basic() -> None:
    """Test different accumulators for each loop using list[list[str]]"""
    sum_so_far = 0
    product_so_far = 1
    list_so_far = []

    with AccumulationTable([["sum_so_far"], ["product_so_far"], ["list_so_far"]]) as table:
        for x in [1, 2, 3]:
            sum_so_far += x
        for y in [2, 3]:
            product_so_far *= y
        for z in [10, 20]:
            list_so_far.append(z)

    # First loop
    assert table.loops[0]["loop_variables"] == {"x": ["N/A", 1, 2, 3]}
    assert table.loops[0]["loop_accumulators"] == {"sum_so_far": [0, 1, 3, 6]}
    assert "product_so_far" not in table.loops[0]["loop_accumulators"]
    assert "list_so_far" not in table.loops[0]["loop_accumulators"]

    # Second loop
    assert table.loops[1]["loop_variables"] == {"y": ["N/A", 2, 3]}
    assert table.loops[1]["loop_accumulators"] == {"product_so_far": [1, 2, 6]}
    assert "sum_so_far" not in table.loops[1]["loop_accumulators"]
    assert "list_so_far" not in table.loops[1]["loop_accumulators"]

    # Third loop
    assert table.loops[2]["loop_variables"] == {"z": ["N/A", 10, 20]}
    assert table.loops[2]["loop_accumulators"] == {"list_so_far": [[], [10], [10, 20]]}
    assert "sum_so_far" not in table.loops[2]["loop_accumulators"]
    assert "product_so_far" not in table.loops[2]["loop_accumulators"]


def test_per_loop_accumulators_empty_list() -> None:
    """Test that a loop can have an empty accumulator list"""
    sum_so_far = 0

    with AccumulationTable([["sum_so_far"], []]) as table:
        for x in [1, 2]:
            sum_so_far += x
        for y in [3, 4]:
            pass

    # First loop
    assert table.loops[0]["loop_accumulators"] == {"sum_so_far": [0, 1, 3]}

    # Second loop
    assert table.loops[1]["loop_accumulators"] == {}
    assert table.loops[1]["loop_variables"] == {"y": ["N/A", 3, 4]}


def test_per_loop_accumulators_multiple_per_loop() -> None:
    """Test multiple accumulators for different loops"""
    sum1 = 0
    count1 = 0
    sum2 = 0
    count2 = 0

    with AccumulationTable([["sum1", "count1"], ["sum2", "count2"]]) as table:
        for x in [5, 10]:
            sum1 += x
            count1 += 1
        for y in [20, 30]:
            sum2 += y
            count2 += 1

    # First loop
    assert table.loops[0]["loop_accumulators"] == {
        "sum1": [0, 5, 15],
        "count1": [0, 1, 2],
    }

    # Second loop
    assert table.loops[1]["loop_accumulators"] == {
        "sum2": [0, 20, 50],
        "count2": [0, 1, 2],
    }


def test_per_loop_accumulators_mismatched_length() -> None:
    """Test assertion when number of accumulator lists doesn't match number of loops"""
    with pytest.raises(
        AssertionError, match="Number of accumulator lists.*must match number of loops"
    ):
        with AccumulationTable([["sum"], ["count"]]) as table:
            for x in [1, 2]:
                pass
            for y in [3, 4]:
                pass
            for z in [5, 6]:  # 3 loops but only 2 accumulator lists
                pass


def test_per_loop_accumulators_with_while_loop() -> None:
    """Test per-loop accumulators with while loops"""
    counter = 0
    total = 0

    with AccumulationTable([["counter"], ["total"]]) as table:
        while counter < 3:
            counter += 1
        for x in [10, 20, 30]:
            total += x

    # First loop
    assert table.loops[0]["loop_accumulators"] == {"counter": [0, 1, 2, 3]}
    assert "total" not in table.loops[0]["loop_accumulators"]

    # Second loop
    assert table.loops[1]["loop_accumulators"] == {"total": [0, 10, 30, 60]}
    assert "counter" not in table.loops[1]["loop_accumulators"]
