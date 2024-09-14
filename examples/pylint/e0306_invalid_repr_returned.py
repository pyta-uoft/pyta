from __future__ import annotations

class Company:
    """A company with some employees."""

    def __init__(self, employees: list[str]) -> None:
        self._employees = employees

    def __repr__(self) -> str:
        return {'employees': self._employees}  # Error on this line
