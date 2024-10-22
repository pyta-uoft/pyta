"""Example for too many nested blocks"""
from __future__ import annotations
from typing import Optional

def cross_join(x_list: list[Optional[int]], y_list: list[Optional[int]],
               z_list: list[Optional[int]]) -> list[tuple[int, int, int]]:
    """Perform an all-by-all join of all elements in the input lists.

    Note: This function skips elements which are None.
    """
    cross_join_list = []
    for x in x_list:  # Error on this line: "Too many nested blocks"
        if x is not None:
            for y in y_list:
                if y is not None:
                    for z in z_list:
                        if z is not None:
                            cross_join_list.append((x, y, z))
    return cross_join_list
