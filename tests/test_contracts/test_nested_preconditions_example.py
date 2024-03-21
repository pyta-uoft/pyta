from python_ta.contracts import check_contracts


@check_contracts
def my_condition1(y: int):
    """
    Preconditions:
    - my_condition2(y)
    """
    return y > 0


@check_contracts
def my_condition2(x: int):
    """
    Preconditions:
    - x > 0
    """
    return x > 0


@check_contracts
def my_function(z: int):
    """
    Preconditions:
    - my_condition1(z)
    """
    return z


@check_contracts
class Student:
    """
    A representation of a student
    """

    name: str
    student_number: int
    gpa: float

    def __init__(self, name, student_number, gpa):
        self.name = name
        self.student_number = student_number
        self.gpa = gpa

    def condition1(self, y):
        """
        Preconditions:
         - self.condition2(y)
        """
        return y > 0

    def condition2(self, x):
        """
        Preconditions:
         - x > 0
        """
        return x > 0

    def function(self, z: int):
        """
        Preconditions:
         - self.condition1(z)
        """
        return z
