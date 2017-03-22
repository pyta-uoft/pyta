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

This is a new project started in the Summer of 2016, and takes the form
of a wrapper around [pylint](pylint.org) (with custom checkers) that operates
directly on Python modules, as well as a website with some supplementary
material going into further detail for the emitted errors.

## Installation

If you're developing PyTA, simply clone this repo.

If you want to just check it out, you can install it using `pip`
(or possibly `pip3` on OSX, depending on what previous versions of
`pip` and Python you have installed):

```
> pip install python-ta
```

## Demo

You can currently see a proof of concept in this repository. Clone it,
and then run `python` in this directory (PyTA is primarily meant to be
included as a library). In the Python interpreter, try running:

```python
>>> import python_ta
>>> python_ta.check_all('examples.forbidden_import_example')
[Some output should be shown]
>>> python_ta.doc('E9999')
```


## Tests

We have a test suite which checks every example file to see if PyTA actually
picks up on the error the file is supposed to illustrate.

To run the tests, enter `python tests/test_examples.py` in the terminal. (If you're on a Mac, you'll likely need to do `python3 tests/test_examples.py` instead.)


## Contributors

Nigel Fong,
Christopher Koehler,
Hayley Lin,
Shweta Mogalapalli,
Jasmine Wu
