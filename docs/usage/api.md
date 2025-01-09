# API

The main entrypoint for running PythonTA's code analysis is the `check_all` function.

```{eval-rst}
.. autofunction:: python_ta.check_all
```

Notes:

- For information on using the `config` argument, see {doc}`Configuration <./configuration>`.
- If using the `ColorReporter`, writing to a file using the `output` argument is not recommended.
  This reporter uses terminal-specific characters to colourize text displayed on your screen, and these characters will look strange when opening the output file in a text editor.

The `doc` function can be used to open the {doc}`PythonTA Checks webpage <../checkers/index>` to look up a specific error.

```{eval-rst}
.. autofunction:: python_ta.doc
```
