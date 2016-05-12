"""pylint: too many instance attributes

Note: the limit is 7 instance attributes.
"""

class MyClass(object):
    """Example with too many instance attributes.
    """

    def __init__(self):
        """
        The are all instance attributes
        """

        self.animal = "Dog"  # These are instance attributes...
        self.bread = "Sourdough"
        self.liquid = "Water"
        self.colour = "Black"
        self.shape = "Circle"
        self.direction = "Up"
        self.clothing = "Shirt"
        self.number = 3
