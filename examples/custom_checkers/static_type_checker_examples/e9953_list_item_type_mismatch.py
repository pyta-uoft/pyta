names: list[str] = ["Alice", "Bob", 3]  # Error: List item 2 has incompatible type "int"; expected "str"

numbers: list[int] = [1, 2, "three"]  # Error: List item 2 has incompatible type "str"; expected "int"

mixed: list[float] = [1.1, 2.2, "3.3"]  # Error: List item 2 has incompatible type "str"; expected "float"
