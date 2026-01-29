# Quick Start

This tutorial is a brief introduction to the different features of PythonTA.

## Installation

In PyCharm:

1. Open the Settings dialog (Windows: File -> Settings..., macOS: PyCharm -> Preferences).
2. Go to **Project <your project name>**, and select **Project Interpreter**.
3. Click on the **+** icon next to the table of installed packages.
4. Search for "`python-ta`", and click **Install Package**.

In the command line:

1. On Windows, run `python -m pip install python-ta`. On macOS or Linux,
   run `python3 -m pip install python-ta`.

## Running PythonTA

PythonTA's code analyzer can be run either through Python code or on the command line.

### Running PythonTA via Python code

**Option 1.**
If you have a Python file you'd like to analyze, you can analyze it by adding the following lines of code:

```python
import python_ta
python_ta.check_all()
```

Here is an [example file called `sample.py`](../demos/sample.py):

```python
"""This file illustrates basic usage of PythonTA's code analysis.
"""


def add_two(x: int, y: int) -> int:
    """Return the sum of x and y.

    PythonTA's analysis of this code will report three issues:

    1. A missing return statement (a logical error)
    2. Missing whitespace around the + (a formatting issue)
    3. The presence of a print call (a code style issue)
    """
    result = x+y
    print(result)


if __name__ == "__main__":
    import python_ta
    python_ta.check_all()
```

When you run this file, PythonTA will analyse this file and open a webpage showing a report of any issues it found.

![An example report produced by PythonTA.](../images/sample_report.png)

Try fixing the above code by adding spaces around the `+`, and replacing `print(result)` with `return result`.
After making these changes, re-run the file: PythonTA's analysis should not find any more issues!

Note: any "𝔄" characters in the source code will be rendered as an "&" in the error message's code snippet.

**Option 2.**
If you don't want to add code to the file being analysed, you can instead call `python_ta.check_all` from outside the file (e.g., in the Python shell, or a separate Python file) and pass in a filename or path:

```python
import python_ta
python_ta.check_all("sample.py")
```

### Running PythonTA via the command line

You can run PythonTA directly from the command line by passing in a filename or path:

```console
$ python_ta sample.py
```

## Learning about the checks

Our {doc}`PythonTA Checks <../checkers/index>` webpage describes all checks that are performed by PythonTA.
Many of these checks originate from Pylint, and more information can be found on the [Pylint documentation website].

You can also look up the documentation for a specific error by its five-character error code (e.g., `E0401`) by calling the `python_ta.doc` function:

```python
python_ta.doc("E0401")
```

This will open up your web browser to the corresponding entry in our documentation page.

## Checking contracts

PyTA supports checking _preconditions_ and _representation invariants_ automatically during the
execution of a Python program. These are parsed automatically from function/class docstrings, and
turned into executable assertions. Type annotations for functions and class instance attributes are
also checked. For examples of both the syntax for specifying contracts and resulting behaviour,
please check out
<https://github.com/pyta-uoft/pyta/blob/master/examples/contracts_demo.py>.

This kind of checking is completely separate from `python_ta.check_all`, and can be enabled by
inserting the following statements in your `if __name__ == '__main__'` block:

```python
if __name__ == '__main__':
    import python_ta.contracts as contracts
    contracts.check_all_contracts()
```

This will add assertions for every function and class in the current module. If you want to
assertions to only a subset of the functions/classes, import and use the decorators
`check_contracts` (for functions) and `add_class_invariants` (for classes) instead.

If you wish to check contracts for your imported modules, pass the module names as arguments
to `check_all_contracts`.

[Pylint documentation website]: https://pylint.readthedocs.io/en/stable/user_guide/checkers/features.html
