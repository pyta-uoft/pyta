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

For help getting started using PyTA: [Quick Start](https://www.cs.toronto.edu/~david/pyta/usage/quick_start.html).

## Installation

If you're interested in using PyTA, you can install it using `pip` (or `pip3`, on OSX/Linux):

```console
> pip install python-ta
```
