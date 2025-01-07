data: dict[int, str] = {1: "one", 2: "two", "three": 3}  # Error: Dict entry 2 has incompatible type "str": "int"; expected "int": "str"

info: dict[str, float] = {"pi": 3.14, "e": 2.71, 42: "1.618"}  # Error: Dict entry 2 has incompatible type "int": "str"; expected "str": "float"
