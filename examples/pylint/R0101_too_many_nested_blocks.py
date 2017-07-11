def cross_join(x_list, y_list, z_list):
    """Perform an all-by-all join of all elements in the input lists,
    skipping elements which are None.
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
