"""pylint: no member
"""


class Rectangle:
    def __init__(self, width, height):
        """
        Initialize the Rectangle.

        @type self: Rectangle
        @type width: int
        @type height: int
        @rtype: None
        """
        self.width = width
        self.height = height

r = Rectangle(5, 4)

# no such member in Rectangle class
print(r.area())  # Error on this line
