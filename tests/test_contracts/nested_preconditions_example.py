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


def validate_student_number(student_number: int):
    """Validate the student number of a student"""
    return student_number > 0


@check_contracts
class Student:
    """
    A representation of a student

    Representation Invariants:
     - validate_student_number(self.student_number)
     - my_function(self.age)
    """

    name: str
    student_number: int
    age: int

    def __init__(self, name, student_number, age):
        self.name = name
        self.student_number = student_number
        self.age = age

    def condition1(self, y: float):
        """
        Preconditions:
         - self.condition2(y)
        """
        return y > 0

    def condition2(self, x: float):
        """
        Preconditions:
         - x > 0
        """
        return x > 0

    def function(self, z: float):
        """
        Preconditions:
         - self.condition1(z)
        """
        return z
