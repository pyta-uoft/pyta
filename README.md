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
of a wrapper around [pylint](https://pylint.org) (with custom checkers) that operates
directly on Python modules, as well as a website with some supplementary
material going into further detail for the emitted errors.

For greater details on the errors PyTA checks for: [Help Documentation](https://www.cs.toronto.edu/~david/pyta/).

For help getting started using PyTA: [Quick Start](https://www.cs.toronto.edu/~david/pyta/quick_start.html).

## Installation

If you're interested in using PyTA, you can install it using `pip` (or `pip3`, on OSX/Linux):

```console
> pip install python-ta
```

If you're developing PyTA, first clone this repo, and then run `pip install -e .[dev]` from inside your local copy of the repo.
Note that some debugging tools require [graphviz](https://www.graphviz.org/download/) to be installed on your system.

### Tests

To run the test suite, run the following command from inside the `pyta` directory:

```console
> python -m pytest tests  # Or python3 on OSX/Linux
```

## Generating the docs

The PyTA documentation is generated using [Sphinx](https://www.sphinx-doc.org/en/master/index.html).
To generate the documentation locally, run the commands:

```console
> cd docs
> make html
```

Then open the file `docs/_build/index.html` in your web browser!

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


## Contributors

Nigel Fong,
Adam Gleizer,
Ibrahim Hasan,
Niayesh Ilkhani,
Rebecca Kay,
Christopher Koehler,
David Kim,
Simeon Krastnikov,
Ryan Lee,
Hayley Lin,
Wendy Liu,
Shweta Mogalapalli,
Ignas Panero Armoska,
Justin Park,
Amr Sharaf,
Kavin Singh,
Alexey Strokach,
Jasmine Wu,
Philippe Yu
