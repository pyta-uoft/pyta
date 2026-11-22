def print_items(items: list[str]) -> None:
    """Print each item in items."""
    for item in items:
        try:
            print(item)
        finally:
            continue
