def add(lst=[]):
    """ Calculates the sum of the elements in the given list.

    @type lst: list
    @rtype: int
    """
    temp = 0
    for item in lst:
        temp += item
    return temp


def add1(lst=[]):
    """ Adds five digits to the end of the list.

    @type lst: list
    @rtype: list
    """
    temp = 5
    for i in range(temp):
        lst.append(i)
    return lst

if __name__ == '__main__':
    print(add1())
    print(add1())
