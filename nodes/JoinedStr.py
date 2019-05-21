"""
JoinedStr astroid node

Represents a list of string expressions to be joined in
f-strings (formatted string literals).

Attributes:
    - values  ([FormattedValue | Const | None])
        - The string expressions to be joined.

Example 1:
    - values -> [Const(value='hello world')]

Example 2:
    - values -> [Const(value='name '),
                 FormattedValue(value=Name(name='name'), format_spec=None),
                 Const(value=', age: '),
                 FormattedValue(value=Name(name='age'), format_spec=None)]

Type-checking:
    - To be documented
"""

# Example 1
F'hello world'

# Example 2
f'name: {name}, age: {age}'
