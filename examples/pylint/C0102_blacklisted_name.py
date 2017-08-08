def pos(obj: int) -> bool:
    foo = obj  # Error on this line: Blacklisted name 'foo'
    return foo < 0
