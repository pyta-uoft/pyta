from typing import List

class Company:
    """A company with some employees."""

    def __init__(self, employees: List[str]) -> None:
        self._employees = employees

    def __str__(self) -> str:
        return {'employees': self._employees}  # Error on this line
