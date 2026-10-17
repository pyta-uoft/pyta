"""This script serves as the entry point for an integration test of the _check watch mode."""

import python_ta

def blank_function() -> int:
    count: int = "ten"
    return count

if __name__ == "__main__":
    python_ta.check_all(config={
        "output-format": "pyta-plain",
        "watch": True
    })
