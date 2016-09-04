<p align="center">
    <img src="https://github.com/pyta-uoft/website/blob/master/images/pyta_logo_markdown.png?raw=true" alt="pyta logo" width="120">
</p>

# PyTA

PyTA is a Python program which uses static code analysis to help students find
and fix common coding errors in introductory Python courses. Python already
has great static analysis tools like pep8 and pylint, but these tools do not
necessarily have the most beginner-friendly format. PyTA has two central goals:

1. Statically identify common coding errors by using existing linting tools and
   building custom linters (e.g., as pylint checkers).
2. Present beautiful, intuitive messages to students that are both helpful for
   fixing errors, and good preparation for the terser messages they will see
   in their careers.

This is a new project I hope to start in the Summer of 2016, and will likely
take the form of a wrapper around pylint (with custom checkers) that operates
directly on Python modules, as well as a website with some supplementary
material going into further detail for the emitted errors.

## Requirements

PyTA supports Python 3 and requires pylint and a few other Python libraries. If you have Python and pip (a
Python package manager, bundled with Python 3.4+), run the following command
to install them:

```
> pip install pylint colorama funcparserlib
```

## Demo

You can currently see a proof of concept in this repository. Clone it,
and then run `python` in this directory (PyTA is primarily meant to be
included as a library). In the Python interpreter, try running:

```python
>>> import pyta
>>> pyta.check_all('examples.forbidden_import_example')
[Some output should be shown]
>>> pyta.doc('E9999')
```


## Tests

We have a test suite which checks every example file to see if PyTA actually
picks up on the error the file is supposed to illustrate.

To run the tests, enter `python tests/test_examples.py` in the terminal.
