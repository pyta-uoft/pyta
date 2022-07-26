"""
Test suite for the AccumulationTable class on different
types of accumulator loops
"""

from python_ta.debug.accumulation_table import AccumulationTable


def test_one_var() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    with AccumulationTable(["sum_so_far"]) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number

    assert table.loop_var_val == ["N/A", 10, 20, 30]
    assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}
    assert table.loop_var_name == "number"


def test_two_var() -> None:
    test_list = [10, 20, 30]
    sum_so_far = 0
    list_so_far = []
    with AccumulationTable(["sum_so_far", "list_so_far"]) as table:
        for number in test_list:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]

    assert table.loop_var_val == ["N/A", 10, 20, 30]
    assert table.loop_accumulators == {
        "sum_so_far": [0, 10, 30, 60],
        "list_so_far": [[], [10], [10, 20], [10, 20, 30]],
    }
    assert table.loop_var_name == "number"


class MyClass:
    items = list

    def __init__(self, items: list):
        self.items = items

    def get_total(self) -> None:

        sum_so_far = 0
        with AccumulationTable(["sum_so_far"]) as table:
            for item in self.items:
                sum_so_far = sum_so_far + item

        assert table.loop_var_val == ["N/A", 10, 20, 30]
        assert table.loop_accumulators == {"sum_so_far": [0, 10, 30, 60]}
        assert table.loop_var_name == "item"


def test_class_var() -> None:
    my_class = MyClass([10, 20, 30])
    my_class.get_total()
