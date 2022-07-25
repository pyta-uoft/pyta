"""
Examples of how to use the AccumulationTable Class with its
respective outputs
"""

import inspect
from typing import Union

from python_ta.debug.accumulation_table import AccumulationTable


def my_func(numbers: list) -> None:
    """Print the Accumulation Table to show the tracking of the respective variables."""
    sum_so_far = 0
    list_so_far = []
    avg_so_far = "N/A"
    with AccumulationTable(["sum_so_far", "list_so_far", "avg_so_far"]):
        for number in numbers:
            sum_so_far = sum_so_far + number
            list_so_far = list_so_far + [number]
            avg_so_far = sum(list_so_far) / len(list_so_far)


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


# class MyClass:
#     curr_total: int
#
#     def __init__(self):
#         self.curr_total = 0
#
#     def get_items(self, items: list) -> None:
#         with AccumulationTable(['self.curr_total']) as table:
#             for item in items:
#                 self.curr_total = self.curr_total + item


if __name__ == "__main__":
    print("my_func function example:")
    my_func([10, 20, 30, 40, 50, 60])
    print("\nRestaurant class example:")
    restaurant = Restaurant()
    restaurant.add_order(["fries", "burger", "soda", "nuggets"])
    restaurant.print_total()

    # The example of MyClass has the issue that if the accumulator variable is not
    # defined in the local scope, i.e. in the scope of the function with the accumulator
    # loop it will run into a Error with the names. In other words, when dealing with
    # accumulation strictly from class attributes, AccumulationTable fails.

    # my_class = MyClass()
    # my_class.get_items([10, 20, 30])
