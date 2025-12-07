"""Python script used for testing that the correct number of error occurrences are being displayed."""

from __future__ import annotations

# The following imports are used solely to trigger errors.
import abc
import math
import os
import sys


def sum_items(lst: list[int]) -> int:
    """..."""
    s = 0
    for i in range(len(lst)):
        s += lst[i]
    return s


def sum_items2(lst: list[int]) -> int:
    """..."""
    s = 0
    for i in range(0, len(lst)):
        s += lst[i]
    return s


def sum_items3(lst: list[int]) -> int:
    """..."""
    s = 0
    for i in range(0, len(lst), 1):
        s += lst[i]
    return s
