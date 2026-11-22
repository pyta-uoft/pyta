from typing import final


@final
class Student:
    """A student class that must not be subclassed."""


class CSStudent(Student):
    """A computer science student that attempts to extend Student."""
