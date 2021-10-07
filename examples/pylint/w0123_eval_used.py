from typing import Any


def dynamic_evaluation(expression: str) -> Any:
    eval(expression)  # Error on this line
