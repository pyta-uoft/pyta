from __future__ import annotations

class Company:
    """A company with some employees."""

    def __init__(self, employees: list[str]) -> None:
        self._employees = employees

    def __bool__(self) -> bool:
        return {'employees': self._employees}  # Error on this line
