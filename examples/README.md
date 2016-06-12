# Standardization of PyTA Examples

## Sorts of Examples

* Custom examples: located in `pyta/examples/`
* PyLint examples: located in `pyta/examples/pylint`


## Purpose

Examples should illustrate an error in a succinct way, while clearly explaining
the cause of the error to a beginner audience.

The examples are included in the website index file with the `pandocfilters`
module. See `/website/index.md` for the syntax to include the examples. Note
that further explanation in addition to the example can be added directly to
the `index.md` file.

## Documentation

#### Module Docstrings

Examples typically do not use module docstrings.


#### Function Docstrings

Function docstrings use double quotes. Try to minimize the vertical size for
compactness on the website.

Type contracts follow the format: `@type <variable_name>: <type>`, and 
`@rtype <type>`

```python
def the_function_name(arg_name1, arg_name2):
    """Brief explanation of ????
    @type arg_name1: <type>
    @type arg_name2: <type>
    @rtype: <type>
    """
    return arg_name1 + arg_name2
```


#### Comments

Write comments in a manner that would be used to talk to a beginner. Be explicit
with clear explanation, and avoid using jargon terms.

Try to point out where the error occurs in the example, if possible. Inline
comments, with two spaces before the has, are useful for this purpose, for
example:

```python
return temp
temp += 1  # Error on this line. This line is unreachable.
```


## Structure

Indent with 4 spaces.

Each example generally has only one class or method.

Examples typically do not need to be executed by calling them, since the
linter checks the examples statically.

Print statements are acceptable, but not necessary.

Imports should be one-per-line, like:

```python
import sys
import math
```


