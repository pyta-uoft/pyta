# PythonTA

Welcome!
PythonTA is a free, open-source suite of educational code analysis tools aimed at novice Python programmers.
It builds on top of professional tools like [pylint], [pycodestyle], and [mypy], with custom feedback messages that are designed to be accessible to beginners and customizable by educators.
It also provides analysis features that occur while code is being executed, including automatic checking of type annotations and logging variable changes across loops.

## Installation and getting started

PythonTA is a pure Python package, and can be installed through [pip](https://pip.pypa.io/en/stable/getting-started/) by running the following command in the terminal:

```console
$ pip install python-ta
```

Then, you can use PythonTA to analyse a Python file from the terminal:

```console
$ python_ta my_file.py
```

or using its Python API:

```python
import python_ta
python_ta.check_all('my_file.py')
```

For a more detailed introduction to PythonTA, check out our {doc}`Quick Start Guide <usage/quick_start>`.

## Acknowledgements

PythonTA is maintained by [David Liu](https://www.cs.toronto.edu/~david/) at the University of Toronto, and has nearly [fifty contributors](https://github.com/pyta-uoft/pyta?tab=readme-ov-file#contributors), most of whom are undergraduate students at the University of Toronto.
This project has received funding from the Faculty of Arts and Science at the University of Toronto.

```{toctree}
:maxdepth: 2
:hidden:

usage/quick_start
checkers/index
usage/configuration
contracts/index
debug/index
cfg/index
```

[pylint]: https://pylint.readthedocs.io/en/latest/
[pycodestyle]: https://pycodestyle.pycqa.org/en/latest/intro.html
[mypy]: https://www.mypy-lang.org/
