"""pylint: abstract class instantiated
Note: doesn't work
"""


class Animal:
    """ A animal in the zoo.
    """

    def __init__(self, b):
        raise NotImplementedError

    def find(self):
        """
        @rtype: None
        """
        raise NotImplementedError


class Lion(Animal):
    """A lion in the zoo.
    """
    def __init__(self):
        super().__init__(5)
        self.find()


class AbstractClass(object):
    def method1(self):
        raise NotImplementedError()

    def method2(self):
        raise NotImplementedError()


class SemiConcreteClass(AbstractClass):
    def method1(self):
        return True


class ConcreteClass(SemiConcreteClass):
    def method2(self):
        fractions = Fraction()
        print(fractions.Fraction("2.0"))
        return True
