# Correct Function Usage
def calculate_area(radius: float) -> float:
    """Calculate the area of a circle."""
    return 3.14159 * radius * radius

area = calculate_area(5.0)

# Proper Variable Assignments
name: str = "Alice"
age: int = 30
height: float = 5.9

# Correct List Usage
names: list[str] = ["Alice", "Bob", "Charlie"]
numbers: list[int] = [1, 2, 3, 4]
prices: list[float] = [9.99, 19.99, 29.99]

# Correct Dict Usage
data: dict[int, str] = {1: "one", 2: "two", 3: "three"}
config: dict[str, float] = {"pi": 3.14, "e": 2.71}

# Valid Operations
result = 10 + 5
value = 3.5 * 2
combined_name = "Alice" + " Bob"

# Union with Compatible Attribute Access
from typing import Union

def get_length(value: Union[str, list]) -> int:
    return len(value)

length_of_name = get_length("Alice")
length_of_list = get_length([1, 2, 3])

# Valid Empty Structures
empty_list: list[int] = []
empty_dict: dict[str, int] = {}

# Functions with Default Arguments
def greet(name: str = "Guest") -> str:
    return f"Hello, {name}"

greeting = greet()
custom_greeting = greet("Alice")
