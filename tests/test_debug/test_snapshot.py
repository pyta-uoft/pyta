"""
Test suite for snapshot functions
"""

import json
import os
import subprocess
import sys

from python_ta.debug.snapshot import snapshot, snapshot_to_json


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


class OneClass:
    """
    Represents a simple class with two primitive attributes.

    Attributes:
        attr1 (str): A string attribute, initialized to "value1".
        attr2 (int): An integer attribute, initialized to 42.
    """

    def __init__(self):
        self.attr1 = "value1"
        self.attr2 = 42


def test_snapshot_to_json_one_class():
    """
    Test snapshot_to_json with snapshot data including an instance of OneClass.
    """
    one_class_instance = OneClass()

    snapshot_data = [
        {"__main__": {"one_class_instance": one_class_instance}},
    ]

    json_data = snapshot_to_json(snapshot_data)

    expected_output = [
        {
            "id": None,
            "isClass": True,
            "name": "__main__",
            "stack_frame": True,
            "value": {"one_class_instance": 1},
        },
        {"id": 2, "isClass": False, "name": "str", "value": "value1"},
        {"id": 3, "isClass": False, "name": "int", "value": 42},
        {
            "id": 1,
            "isClass": True,
            "name": "OneClass",
            "value": {"attr1": 2, "attr2": 3},
        },
    ]

    assert json_data == expected_output
