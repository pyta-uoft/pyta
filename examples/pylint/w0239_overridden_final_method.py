from typing import final


class Student:
    """A student."""

    @final
    def get_program(self) -> str:
        """Return this student's program of study."""
        return "Undeclared"


class CSStudent(Student):
    """A computer science student."""

    def get_program(self) -> str:
        """Return this student's program of study."""
        return "Computer Science"
