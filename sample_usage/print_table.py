"""Examples for the python_ta.debug.AccumulationTable class.
"""
from __future__ import annotations

from typing import Union

from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers."""
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"]):
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    return list_so_far


class Restaurant:
    """Restaurant class to process food orders"""

    _menu: dict[str, float]
    _current_order: list[str]

    def __init__(self) -> None:
        self._menu = {"fries": 3.99, "burger": 7.99, "soda": 2.99, "nuggets": 4.99, "coffee": 1.99}
        self._current_order = []

    def add_order(self, items: Union[str, list[str]]) -> None:
        """Add order(s) to the current orders"""
        if isinstance(items, str):
            if items in self._menu:
                self._current_order.append(items)
        else:
            for item in items:
                if item in self._menu:
                    self._current_order.append(item)

    def print_total(self) -> None:
        """Print the accumulation table displaying the price of each item
        and the total after each item
        """
        curr_item_price = 0.0
        curr_total = 0.0
        with AccumulationTable(["curr_item_price", "curr_total"]):
            for item in self._current_order:
                curr_item_price = self._menu[item]
                curr_total += curr_item_price


if __name__ == "__main__":
    print("calculate_sum_and_averages([10, 20, 30, 40, 50, 60])")
    calculate_sum_and_averages([10, 20, 30, 40, 50, 60])
    print("")

    print("\nRestaurant class example:")
    restaurant = Restaurant()
    restaurant.add_order(["fries", "burger", "soda", "nuggets"])
    restaurant.print_total()
