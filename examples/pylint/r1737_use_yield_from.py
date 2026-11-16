from collections.abc import Iterable, Iterator


def yield_items(items: Iterable[int]) -> Iterator[int]:
    """Yield the values in items."""
    for item in items:  # Error on this line
        yield item
