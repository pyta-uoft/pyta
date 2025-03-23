"""This script serves as the entry point for an integration test of the _check watch mode."""

import logging
import python_ta

# Ensure INFO logs are shown in stderr
logging.basicConfig(level=logging.DEBUG)

def blank_function() -> int:
    count: int = "ten"
    return count

if __name__ == "__main__":
    python_ta.check_all(config={
        "output-format": "python_ta.reporters.PlainReporter",
        "watch": True
    })
