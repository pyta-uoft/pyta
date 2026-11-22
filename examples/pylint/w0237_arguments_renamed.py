class Student:
    """A student."""

    def introduce(self, name: str) -> str:
        """Return an introduction for name."""
        return f"Hello, my name is {name}."


class CSStudent(Student):
    """A computer science student."""

    def introduce(self, student_name: str) -> str:
        """Return an introduction for student_name."""
        return f"Hello, my name is {student_name}, and I study computer science."
