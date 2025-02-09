# Configuration

PythonTA supports configuration through an "rc file" in the [INI format](https://docs.python.org/3/library/configparser.html).
A custom configuration file can be passed in the command-line using the `--config <path>` option,
and to `python_ta.check_all` with the `config=<path>` argument.
Additionally, a dictionary containing key-value pairs corresponding to configuration options may be passed as the `config` argument to `python_ta.check_all`.
In all cases, custom configuration options are merged with PythonTA's default configuration.

## Example

The following configuration file can be used to configure PythonTA to set a maximum line length of 120 and to print its report as plain text, rather than on a webpage.

```ini
# config.ini
[REPORTS]
output-format = python_ta.reporters.PlainReporter

[FORMAT]
max-line-length = 120
```

This configuration file can be used when checking a Python module `my_file.py` as follows:

- In the command-line: `python_ta --config config.ini my_file.py`
- Using the Python API: `python_ta.check_all("my_file.py", config="config.ini")`

The same configuration options may be passed directly to `python_ta.check_all` as key-value pairs in a dictionary:

```python
import python_ta
python_ta.check_all("my_file.py", config={
    "output-format": "python_ta.reporters.PlainReporter",
    "max-line-length": 120
})
```

## Pylint configuration options

PythonTA supports all [Pylint configuration options](https://pylint.readthedocs.io/en/stable/user_guide/configuration/index.html).
By default, PythonTA sets the following default values for Pylint's configuration options.

| Pylint option     | Pylint default               | PythonTA default                        |
| ----------------- | ---------------------------- | --------------------------------------- |
| max-nested-blocks | 5                            | 3                                       |
| max-line-length   | 100                          | 80                                      |
| ignore-long-lines | `^\s*(# )?<?https?://\S+>?$` | `^\s*((# )?<?https?://\S+>?)\|(>>>.*)$` |
| disable           | `()`                         | See below                               |
| output-format     | text                         | `"python_ta.reporters.HTMLReporter"`    |

You can disable this behaviour by passing `load_default_config=False` to `python_ta.check_all`.
In this case, Pylint's default configuration will be used instead, though all custom PythonTA options described below will still retain their default values.

### PythonTA reporters

PythonTA offers four different types of reporters used to display the results of its analysis.
These may be set using the `output-format` configuration option.

- `python_ta.reporters.PlainReporter`: outputs report in plain text
- `python_ta.reporters.ColorReporter`: outputs a colourized report (can only be used in the terminal/Python shell)
- `python_ta.reporters.JSONReporter`: outputs a JSON representation of the messages reported
- `python_ta.reporters.HTMLReporter`: outputs report in a webpage

### Disabled Pylint checks

The following Pylint checks are disabled by default.
You can re-enable them by using the `enable` option.

```text
E0100, E0105, E0106, E0110, E0112, E0113, E0114, E0115, E0116, E0117, E0118,
E0236, E0237, E0238, E0240, E0242, E0243, E0244, E0305, E0308, E0309, E0310, E0311, E0312, E0313,
E0402,
E0603, E0604, E0605, E0606,
E0703, W0707,
E1124, E1125, E1132, E1139, E1142,
E1200, E1201, E1205, E1206,
E1300, E1301, E1302, E1303, E1304,
W1406,
E1507, E1519,
E1700, E1701,
W0120, W0131, W0135, W0150, W0177,
W0213, W0235, W0236, W0238, W0244, W0246,
W0601, W0602, W0614, W0640,
W1113, W1115,
W1300, W1301, W1302, W1306, W1307,
W1502, W1503, W1505, W1506, W1507, W1508, W1509, W1510, W1511, W1512, W1513, W1514, W1518,
C0103, C0105, C0131, C0132,
C0200, C0202, C0203, C0204, C0205, C0206, C0207, C0208,
C0327, C0328,
R0202, R0203, R0206,
R0901, R0903, R0904, R0911, R0917,
R1703, R1705, R1706, R1708, R1709, R1710, R1711, R1717, R1718, R1719, R1720, R1722, R1723, R1724,
R1728, R1729, R1730, R1731,
C1803,
F0202,
W0402, W0407,
W0603,
W1201, W1202,
I0023,
I1101,
C9960,
lambda-expressions,
similarities,
spelling,
threading,
unnecessary-dunder-call,
unsupported_version,
E2502, E2510, E2511, E2512, E2513, E2514, E2515,
missing-timeout, positional-only-arguments-expected
```

## PythonTA general configuration options

The following options are used to configure the general behaviour of PythonTA.

### `pyta-number-of-messages` (default: `0`)

The maximum number of occurrences of each check to report.
This option can be used to limit the size of the output report.
If set to 0 (the default), all occurrences are shown.

### `pyta-template-file` (default: `"template.html.jinja"`)

HTML template file for the HTMLReporter.

### `allow-pylint-comments` (default: `false`)

When `false` (the default), raise an error when analysing code with comments that contain [`pylint:` directives](https://pylint.readthedocs.io/en/stable/user_guide/messages/message_control.html#block-disables).
When `true`, allows these comments, which can be used to disable error checks in specific blocks of code.

### `z3` (default: `false`)

When `true`, uses the [Z3 theorem prover](https://github.com/Z3Prover/z3) to enhance code analysis.
Requires the `python-ta[z3]` group to be installed.

### `use-pyta-error-messages` (default: `true`)

When `true`, replace some of Pylint's error messages with custom PythonTA versions.
PythonTA's error messages can be seen in the source file [messages_config.toml](https://github.com/pyta-uoft/pyta/blob/master/python_ta/config/messages_config.toml).

### `messages-config-path` (default: PythonTA's `messages_config.toml`)

The path to a TOML file to use to replace Pylint's and PythonTA's default error messages.
This allows users to provide their own messages for specific checks.
This option is not affected by the `use-pyta-error-messages` option.

### `watch` (default: `false`)

When `true`, the HTMLReporter runs as a persistent server that continuously serves the PyTA report.
This allows users to refresh the report page in their browser without restarting the server.
When `false` (the default), the server responds to a single request and then shuts down. Modification
to this configuration option has no effect for the other reporters.

### `server-port` (default: `0`)

The server-port option specifies the port number to use when serving the PyTA HTML report. When set to 0 (the default),
the server automatically selects an available port. If set to a specific port (e.g., 5008), the server attempts
to bind to that port. This configuration option only applies to the HTMLReporter and does not affect other reporters.

## PythonTA checker configuration options

The following options are used to configure the behaviour of specific checks.

### `pycodestyle-ignore`

A list of [pycodestyle error codes](https://pycodestyle.pycqa.org/en/latest/intro.html#error-codes) to disable when running the **pep8-errors** check.
By default, the following pycodestyle error codes are ignored, largely due to overlap with existing pylint checks.

- E111, E112, E113, E114, E117, E401, E402, E501, E701, E702, E703, E711, E712, E722, E741, E742,
  E743, E901, W291, W292, W293, W391, W503, W605

### `allowed-io`

A list of function names and [qualified method names](https://docs.python.org/3/glossary.html#term-qualified-name) to ignore when performing the **forbidden-io** check.
By default, this is `()`.

### `ignore-names`

A regular expression that matches function, class, and variable names to ignore when performing the **naming-convention-violation** check.
By default, this is an empty string, meaning no names are ignored.

### `ignore-module-names`

A regular expression that matches module names to ignore when performing the **module-name-violation** check.
By default, this is an empty string, meaning no names are ignored.

### `allowed-import-modules`

A list of module names that are permitted by the **forbidden-import** check.
It is recommended to not modify this option, and instead modify the `extra_imports` option.

By default, the following modules are allowed:

- `dataclasses`, `doctest`, `unittest`, `hypothesis`, `pytest`, `python_ta`, `python_ta.contracts`, `timeit`, `typing`, `__future__`

### `extra-imports`

A list of additional module names that are permitted by the **forbidden-import** check.
By default, this list is empty.
Modules added to this list are permitted in addition to the ones listed in `allowed-import-modules`.

### `allow-local-imports`

When `true`, allow all local modules to be imported, without being reported by the **forbidden-import** check.
By default this option is `false`.

### `mypy-options`

A list of [command-line arguments](https://mypy.readthedocs.io/en/stable/command_line.html) to be passed into mypy when performing the [**static type** checks](#mypy-based-checks).

By default, this list includes the following flags:

- `ignore-missing-imports`, `follow-imports=skip`

Modifying this option will override all default flags.
Note that the `show-error-end` flag is always passed into mypy, so it does not need to be specified within this option.
