"""
JoinedStr astroid node

Represents a list of string expressions to be joined in
f-strings (formatted string literals).

Attributes:
    - values    (Optional[list[FormattedValue | Const]])
        - The string expressions to be joined.

Example 1:
    JoinedStr(values=[Const(value='hello world')])

Example 2:
    JoinedStr(values=[
        Const(value='name: '),
        FormattedValue(
            value=Name(name='name'),
            format_spec=None),
        Const(value=', age: '),
        FormattedValue(
            value=Name(name='age'),
            format_spec=JoinedStr(values=[Const(value='.0f')]))])

* Note that there is another JoinedStr in the format_spec of the FormattedValue.
This JoinedStr contains a str Const representing how to format a FormattedValue value

Type-checking:
    - To be documented
"""

# Example 1
f'hello world'

# Example 2
f'name: {name}, age: {age:.0f}'
