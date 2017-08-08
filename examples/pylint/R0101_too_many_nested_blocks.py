from typing import List, Tuple, TypeVar, Union

T = TypeVar('T')
TN = Union[T, None]

def cross_join(x_list: List[TN], y_list: List[TN],
               z_list: List[TN]) -> List[Tuple[T, T, T]]:
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
