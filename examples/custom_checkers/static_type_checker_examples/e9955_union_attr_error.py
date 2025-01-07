from typing import Union

def get_status(status: Union[str, int, float]) -> str:
    return (status
            .upper())  # Error: Item "int" of "str | int | float" has no attribute "upper"
                           # Error: Item "float" of "str | int | float" has no attribute "upper"

def get_keys(data: Union[dict, list]) -> list:
    return data.keys()  # Error: Item "list" of "dict | list" has no attribute "keys"
