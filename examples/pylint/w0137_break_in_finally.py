def print_first_item(items: list[str]) -> None:
    """Print the first item in items."""
    for item in items:
        try:
            print(item)
        finally:
            break
