# Standardization of PyTA Examples


## Purpose

Examples should illustrate an error in a succinct way, while clearly explaining
the cause of the error to a beginner audience.


## Sorts of Examples

* Custom examples: located in `python_ta/examples/`
* PyLint examples: located in `python_ta/examples/pylint/`


## How Examples are Included

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

Write comments in a manner that would be used to explain to a beginner. Be 
explicit with clear explanation, and avoid using jargon.

Try to point out where the error occurs in the example, if possible. Inline
comments, with two spaces before the hash symbol, are useful for this purpose, for
example:

```python
return temp
temp += 1  # Error on this line. This line is unreachable.
```


## Structure

Imports (if needed) should be one-per-line, like:

```python
import sys
import math
```

Use single quotes, unless specified otherwise.

Indent with 4 spaces.

Each example generally has only one class or function.

Examples typically do not need to be executed by calling them, since the
linter checks the examples statically.

Print statements should be avoided.


## Correctness

Examples should be compliant with the [PEP 8](https://www.python.org/dev/peps/pep-0008/) style guide, where possible. The [pycodestyle](https://github.com/PyCQA/pycodestyle) tool can be used to check for compliance with PEP 8.

Some messages are allowed in the examples:

```
Invalid module name
Missing module docstring
Invalid constant name
```

Examples should be checked with PyTA to ensure the intended message is raised. Extraneous messages should be limited in a well-crafted example.
