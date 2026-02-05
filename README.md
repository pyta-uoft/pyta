# PythonTA

Welcome! This is the repository for PythonTA.
For more information about the library, check out our [documentation website](https://www.cs.toronto.edu/~david/pyta/) or the [package README.md](./packages/python-ta/README.md).

## Development

If you're developing PyTA:

1. First, clone this repository.
2. Open a terminal in this repo, and run `pip install -e "./packages/python-ta-z3" "./packages/python-ta[dev, cfg, z3]"` to install the dependencies.
3. Then run `pre-commit install` to install the pre-commit hooks (for automatically formatting and checking your code on each commit).

While not strictly necessary for debugging, some debugging tools require [graphviz](https://www.graphviz.org/download/) to be installed on your system.

### Tests

To run the test suites, run the following commands from inside the `pyta` directory:

```console
> python -m pytest packages/python-ta/tests  # Or python3 on OSX/Linux
> python -m pytest packages/python-ta-z3/tests  # Or python3 on OSX/Linux
```

### Generating the docs

The PyTA documentation is generated using [Sphinx](https://www.sphinx-doc.org/en/master/index.html).
To generate the documentation locally, run the commands:

```console
> cd packages/python-ta/docs
> make html
```

Then open the file `packages/python-ta/docs/_build/html/index.html` in your web browser!

### Demo

You can currently see a proof of concept in this repository. Clone it,
and then run `python` in this directory (PyTA is primarily meant to be
included as a library). In the Python interpreter, try running:

```python
>>> import python_ta
>>> python_ta.check_all('examples.custom_checkers.e9999_forbidden_import')
[Some output should be shown]
>>> python_ta.doc('E9999')
```

## Contributors

Ibrahim Bilal,
Lorena Buciu,
Simon Chen,
Freeman Cheng,
Ivan Chepelev,
Yianni Culmone,
Daniel Dervishi,
Nigel Fong,
Adam Gleizer,
James Han,
Ibrahim Hasan,
Niayesh Ilkhani,
Craig Katsube,
Rebecca Kay,
Christopher Koehler,
David Kim,
Simeon Krastnikov,
Ryan Lee,
Christopher Li,
Hoi Ching (Herena) Li,
Hayley Lin,
Bruce Liu,
Merrick Liu,
Wendy Liu,
Yibing (Amy) Lu,
Maria Shurui Ma,
Zain Mahmoud,
Aina Fatema Asim Merchant,
Karl-Alexandre Michaud,
Shweta Mogalapalli,
Ignas Panero Armoska,
Justin Park,
Harshkumar Patel,
Varun Sahni,
Eleonora Scognamiglio,
Stephen Scott,
Amr Sharaf,
Richard Shi,
Kavin Singh,
Alexey Strokach,
Sophy Sun,
Praneeth Suryadevara,
Ali Towaiji,
Utku Egemen Umut,
Sarah Wang,
Lana Wehbeh,
Jasmine Wu,
Raine Yang,
Philippe Yu,
Shirley Zhang,
Yi Cheng (Michael) Zhao
