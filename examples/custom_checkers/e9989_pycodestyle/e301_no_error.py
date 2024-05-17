"""Does not trigger E301"""


class Example:
    """does not trigger E301 error"""
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def getx(self):
        """returns x"""
        return self.x

    def gety(self):
        """returns y"""
        return self.y
