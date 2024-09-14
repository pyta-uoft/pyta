from __future__ import annotations
from typing import Optional


def index_of(numbers: list[int], n: int) -> Optional[int]:
    """Return the index of the first occurrence of n in numbers,
    or None if n doesn't appear in the list.
    """
    i = 0
    for number in numbers:
        if number == n:
            return i
        i += 1


def day_name_to_number(day: str) -> int:
    """Return a number between 0-6 representing the given day of the week."""
    if day == 'Monday':
        return 0
    elif day == 'Tuesday':
        return 1
    elif day == 'Wednesday':
        return 2
    elif day == 'Thursday':
        return 3
    elif day == 'Friday':
        return 4
    elif day == 'Saturday':
        return 5
    elif day == 'Sunday':
        return 6
