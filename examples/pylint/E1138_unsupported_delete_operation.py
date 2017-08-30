from typing import List

class NamedList:
    """A contaner class for storing a list of named integers."""

    def __init__(self, names: List[str], values: List[int]) -> None:
        self._names = names
        self._values = values

    def __getitem__(self, name: str) -> int:
        idx = self._names.index(name)
        return self._values[idx]

    def __contains__(self, name: str) -> bool:
        return name in self._names


named_list = NamedList(['a', 'b', 'c'], [1, 2, 3])
print('c' in named_list)  # Prints True
del named_list['c']  # Error on this line
print('c' in named_list)
