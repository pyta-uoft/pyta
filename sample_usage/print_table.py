import sys

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

    def add_order(self, item: str) -> None:
        if item in self._menu:
            self._current_order.append(item)

    def print_total(self) -> float:
        curr_item_price = 0.0
        curr_total = 0.0
        with AccumulationTable(["curr_item_price", "curr_total"]):
            for item in self._current_order:
                curr_item_price = self._menu[item]
                curr_total += curr_item_price

        return curr_total


if __name__ == "__main__":
    print("my_func function example:")
    my_func([10, 20, 30, 40, 50, 60])
    print("\nRestaurant class example:")
    restaurant = Restaurant()
    restaurant.add_order("fries")
    restaurant.add_order("burger")
    restaurant.add_order("soda")
    restaurant.add_order("nuggets")
    restaurant.print_total()
