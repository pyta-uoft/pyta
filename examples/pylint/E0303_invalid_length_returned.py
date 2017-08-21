from typing import List

class Company:

    def __init__(self, employees: List[str]) -> None:
        self._employees = employees

    def __len__(self) -> int:
        return -1  # Error on this line
