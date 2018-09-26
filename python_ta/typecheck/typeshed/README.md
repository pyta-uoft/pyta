# Typeshed modifications

* old: `str.__contains__(self, s: object) -> bool`

  new: `str.__contains__(self, s: str) -> bool`

* old: `bytes.__contains__(self, o: object) -> bool`

  new: `bytes.__contains__(self, o: bytes) -> bool`

* old: `list.__contains__(self, o: object) -> bool`

  new: `list.__contains__(self, x: _T) -> bool`

* old: `dict.__contains__(self, o: object) -> bool`

  new: `dict.__contains__(self, o: _T) -> bool`

* old: `set.__contains__(self, o: object) -> bool`

  new: `set.__contains__(self, element: _T) -> bool`

* old: `frozenset.__contains__(self, o: object) -> bool`

  new: `frozenset.__contains__(self, element: _T) -> bool`

* old: `range.__contains__(self, o: object) -> bool`

  new: `range.__contains__(self, i: int) -> bool`

* old: `slice.__init__(self, start: Optional[int], stop: Optional[int], step: int = None) -> None`

  new: `slice.__init__(self, start: Optional[int], stop: Optional[int], step: Optional[int] = None) -> None`

* old: `class int(SupportsInt, SupportsFloat, SupportsAbs[int]):`

  new: `class int(SupportsInt, SupportsFloat, SupportsComplex, SupportsAbs[int]):`

* old: `class float(SupportsFloat, SupportsInt, SupportsAbs[float]):`

  new: `class float(SupportsFloat, SupportsInt, SupportsComplex, SupportsAbs[float]):`

* old: `class complex(SupportsAbs[float])`

  new: `class complex(SupportsComplex, SupportsAbs[float])`

* old: --

  new: Added class `Iterator` (from `typing.pyi`)
