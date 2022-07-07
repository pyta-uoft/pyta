import sys

from python_ta.debug.accumulation_table import AccumulationTable


def my_func(numbers: list) -> None:
    """Print the Accumulation Table to show the tracking of the respective variables."""
    sum_so_far = 0
    list_so_far = []
    avg_so_far = "N/A"
    with AccumulationTable(["sum_so_far", "list_so_far", "avg_so_far"]) as table:
        for number in numbers:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]
            avg_so_far = sum(list_so_far) / len(list_so_far)
            # table.add_iteration([sum_so_far, list_so_far, avg_so_far], number)


if __name__ == "__main__":
    my_func([10, 20, 30, 40, 50, 60])
