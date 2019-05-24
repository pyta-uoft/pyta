"""
FormattedValue astroid node

Represents a single formatting field in an f-string (formatted string literal).

Attributes:
    - value  (Expr)
        - The value to be formatted into the string.
    - format_spec  (JoinedStr | None)
        - The formatting to be applied to the value.

Example 1:
    * NOTE : The example below is of a FormattedValue Node "{name}" within
             a JoinedStr Node "f'My name is {name}'".

    - value       -> Name(name='name')
    - format_spec -> None

Example 2:
    * NOTE : The example below is of a FormattedValue Node "{3.14159:.3}'" within
                 a JoinedStr Node "f'{3.14159:.3}'".

    - value       -> Const(value=3.14159)
    - format_spec -> JoinedStr(values=[Const(value='.3')])

Type-checking:
    - To be documented
"""

# Example 1
f'My name is {name}'

# Example 2
f'{3.14159:.3}'
