"""pylint: too many instance attributes

Used when class has too many instance attributes, try to reduce this to get a
simpler (and so easier to use) class.

Default: 7
"""
# pylint: disable=too-few-public-methods, invalid-name

class MyClass(object):
    """Example with class attributes that will be set as instance attributes
    later.
    """
    animal = "Dog"  # These are class attributes...
    bread = "Sourdough"
    liquid = "Water"
    colour = "Black"
    shape = "Circle"
    direction = "Up"
    clothing = "Shirt"
    number = 3

class_instance = MyClass()
class_instance.animal = "Cat"  # These are instance attributes...
class_instance.bread = "Rye"
class_instance.liquid = "Juice"
class_instance.colour = "Green"
class_instance.shape = "Hexagon"
class_instance.direction = "Left"
class_instance.clothing = "Socks"
class_instance.number = 10
