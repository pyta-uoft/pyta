# Quick Start

This webpage is a brief introduction to PyTA, mainly intended for students in first-year computer
science students at the University of Toronto.

## Installation

In PyCharm:

1. Open up the Settings dialog (Windows: File -> Settings..., Mac: PyCharm -> Preferences).
2. Go to Project <your project name>, and select Project Interpreter.
3. Make sure you have the right version of Python selected in the "Project Interpreter" dropdown.
4. Click on the green **+** icon on the right side.
5. Search for `python-ta`, and press "Install Package".

In the command-line:

1. On Windows, run `python -m pip install python-ta`. On macOS or Linux,
   run `python3 -m pip install python-ta` (as running just `python` will likely refer to an older
   version of Python).

## Starting out

The easiest way to run PyTA on a file is very similar to `doctest`. Include the following lines in
the `if __name__ == '__main__'` block of your file:

```python
if __name__ == '__main__':
    import python_ta
    python_ta.check_all()
```

Then when you run the file, PyTA will check your code in that file. By default, a page will open in
your web browser showing a PyTA report.

### Running PyTA in the Python interpreter

You can also run PyTA in the Python interpreter (in PyCharm, this is called the Python Console) and
run the following command:

```python
>>> import python_ta
```

Then you can begin checking Python modules. You can check any Python file in the current directory.
For example, if you have a file called 'hello.py', you can check it as follows:

```python
>>> python_ta.check_all('hello.py')
```

If you want to check a file which is in a subdirectory of your current location, simply write the (
relative) path to the file.

On Windows, use double backslashes to separate folders:

```python
>>> python_ta.check_all('subfolder1\\sub2\\a\\my_file.py')
```

On macOS/Linux, use a forward slash instead:

```python
>>> python_ta.check_all('subfolder1/sub2/a/my_file.py')
```

## Errors vs. warnings

PyTA distinguishes between two types of checks:

- logical errors and use of forbidden language features
- style errors or violating chosen conventions

The output of `python_ta.check_all` divides the messages into two sections. Note that the headings
will always appear, even if you don't have any errors. If there aren't any errors listed, the
sections will simply be empty.

If you want to only see the logical errors and forbidden features
(useful for debugging purposes), use `python_ta.check_errors` instead of `python_ta.check_all`:

```python
>>> python_ta.check_errors('hello.py')
```

## Accessing the documentation

We have a [separate PyTA webpage](https://www.cs.toronto.edu/~david/pyta/)
describing the errors that PyTA checks for. If you find yourself wondering what an error message
means, you can look up the error by its five-character error code (which is always of the
form `E0401`) and look it up on our website. Or, in the Python interpreter you can call
the `python_ta.doc` function on the code:

```python
>>> python_ta.doc('E0401')
```

This will open up your web browser to the corresponding entry in our documentation page.

## Checking contracts

PyTA supports checking *preconditions* and *representation invariants* automatically during the
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
