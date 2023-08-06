# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Enhancements

- Can now create control flow graphs to visualize the execution of your program.
- Added support to allow the user to configure how control flow graphs are generated.
- The `TopLevelCodeChecker` now allows type alias assignment statements at the top level, i.e., doesn't flag such lines
  of code as an error.
- The `GlobalVariablesChecker` now allows type alias assignment statements at the top level, i.e., doesn't flag such
  lines of code as an error.
- For the message display of C0303 `trailing-whitespace`, trailing whitespaces are now appearing in the reporters,
  and only those spaces are highlighted rather than the entire line of code.
- The `UnnecessaryIndexingChecker` now checks for a greater variety of loop/comprehension indexes.
- Modified configuration behaviour so when providing a config file, it only needs to contain the configuration options you want overridden.
- Added the option `load_default_config` to `check_errors` and `check_all` to specify whether to automatically load the PythonTA default config.
- For the message display of E9989 `pep8-errors`, all "blank line" messages are now custom-rendered, i.e., blank lines
  are now highlighted instead of function signatures and instruction strings are added for required blank lines that
  are missing.
- When running `check_contracts` on a class with type aliases as type annotations for its attributes, the `NameError`
  that appears (which indicates that the type alias is undefined) is now resolved.
- The default value of `pyta-number-of-messages` is now 0. This automatically displays all occurrences of the same error.
- For the contract checking `new_setattr` function, any variables that depend only on `klass` are now defined in the
  outer function, efficiency of code was improved, and the attribute value is now restored to the original value if the
  `_check_invariants` call raises an error.
- Added new function `validate_invariants` which takes in an object and checks that the representation invariants of the object are satisfied.
- The check for `ENABLE_CONTRACT_CHECKING` is now moved to the top of the body of the `new_setattr` function.
- Added the file `conftest.py` to store `pytest` fixtures.
- Updated to [pycodestyle v2.11](https://github.com/PyCQA/pycodestyle/blob/main/CHANGES.txt).

### Bug Fixes

- Fixed bug where running `python3 -m python_ta --generate-config` yields a `FileNotFoundError`.
- Fixed bug in how PythonTA reports error messages that occur when parsing configuration files.
- Fixed bug where the HTML reporter would display all error occurrences of the same type despite stating that only a limited number was being shown.
- Fixed bug where the JSON reporter was not limiting the number of error occurrences displayed with respect to `pyta-number-of-messages`.
- Ensured some config file parsing errors no longer display incorrect lines of code as the source of the error.
- Remove line double-spacing in PlainReporter and ColorReporter output code snippets.

### New checkers

Custom checkers:

- `invalid-name-checker`: Provide beginner-friendly error messages when reporting variable names that violate Python naming conventions.

Pylint checkers v2.16:

- `pointless-exception-statement`
- `shadowed-import`
- `unbalanced-dict-unpacking`
- `nested-min-max`
- `invalid-slice-step`

Pylint checkers v2.17:

- `bad-chained-comparison`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

## [2.5.0] - 2023-04-27

### Bug fixes

- Fixed bug in possibly-undefined checker where a comprehension variable is falsely flagged as possibly undefined.
- Fixed bug where `check_errors` and `check_all` opens a webpage when a nonexistent or unreadable path is passed as an argument.
- Fixed the CFG implementation to resolve a bug in the possibly-undefined checker where variables were falsely flagged as possibly undefined when the code conditionally raises an exception and the variable was referenced afterwards.
- Fixed bug where the generated CFGs will highlight the except block as unreachable if the same exception it is handling was raised in the body of the tryexcept.

### New checkers

Custom checkers:

- `forbidden-python-syntax`: Flag code that is not permitted to be used on an assessment.

### Other

- Pin dependency versions

## [2.4.2] - 2023-1-31

### Bug fixes

- Fixed custom message formats based on Pylint 2.15 updates.
- Fixed bug in shadowing-in-comprehension checker when target is a subscript node.
- Ensured `check_contracts` and `check_all_contracts` do nothing when `ENABLE_CONTRACT_CHECKING` is `False`.

## [2.4.1] - 2023-1-13

### Bug fixes

- Fixed PyTA contract checking for method calls when running modules in PyCharm using the "Run File in Python Console" action.

## [2.4.0] - 2022-12-21

### Enhancements

- `unnecessary_indexing_checker` has now been extended to check comprehensions in addition to for loops.
- `invalid_for_target_checker` has now been extended to check comprehensions in addition to for loops.
- `forbidden_io_function_checker` is now able to check for calls to IO functions written at the top-level of a module, but outside the main block.
- `python_ta.debug.AccumulationTable` is extended to support printing loop iterations for while loops.
- Violated representation invariant error message now includes the class name and current values of the instance attributes.
- Added constant `python_ta.contracts.ENABLE_CONTRACT_CHECKING` to only check contracts when its value is set to `True`.
- `python_ta.debug.AccumulationTable` has extended loop detection to allow the loop to appear anywhere inside the with statement.

### Bug Fixes

- Fixed Issue #831: Contract Checker Bug. Now raises `AssertionError` when the expected type is `float` but got `int` instead.
- PyTA contracts' type checking now raises `AssertionError` when the expected type is `int` but got `bool` instead.
- Fixed PyTA contract checking when running modules in PyCharm using the "Run File in Python Console" action.

### New checkers

Custom checkers:

- `forbidden-top-level-code`: Flag code written at the top level when it is not one of the four acceptable types.

## [2.3.3] - 2022-09-05

### Bug fixes

- Restored 'line_end', 'column_end', and 'snippet' fields in JSON reporter output.

## [2.3.2] - 2022-08-30

### Bug fixes

- Updated jsonreporter to get data from the new pylint Message class (#840)

### Experimental

- Added preliminary support for translation of constraints into Z3 solver.
  (This is currently not enabled by default in PythonTA.)

## [2.3.1] - 2022-08-08

### Bug fixes

- Add missing `toml` package to library dependencies.
- Improve formatting of `None` and `float`s in `AccumulationTable` display.
  Also make minor improvements to the documentation.

## [2.3.0] - 2022-08-08

### Enhancements

- Added new command line argument `-v/--version`. User can print out current PythonTA version using `python -m python_ta -v`.
- Preconditions, postconditions, and representation invariants are now parsed only once and compiled.
- Can configure custom error messages for pylint in a toml file.
- `missing_space_in_doctest_checker` is now able to check doctests in python modules and classes.
- Updated to Pylint v2.14. See "New checks" below for the new checkers enabled by default.
- Added new `python_ta.debug` module with an `AccumulationTable` context manager for loop print debugging.
- Improve message for R1710 (inconsistent-return-statements)

### Bug fixes

- Function `check_all_contracts` skips contract checks for functions and classes which are not defined in a module whose name is passed as an argument. If `decorate_main` argument is `True`, functions and classes defined in `__main__` module will be checked without needing to pass in additional arguments.

### New checkers

Custom checkers:

- `type-is-assigned`: Flag when a type is not annotated but rather assigned in a function or class definition.

Pylint checkers v2.13:

- `modified-iterating-list`
- `modified-iterating-dict`
- `modified-iterating-set`
- `unnecessary-ellipsis`
- `bad-file-encoding`

Pylint checkers v2.14:

- `comparison-of-constants`
- `potential-index-error`
- `unnecessary-list-index-lookup`
- `duplicate-value`
- `super-without-brackets`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

## [2.2.0] - 2021-12-09

### Enhancements

- Added support for postconditions in function docstring.
- Improve error message of `unncessary-indexing` checker.
- Added CLI for `python_ta.contracts` module for executing a file with contract checking
  (`$ python -m python_ta.contracts FILE`)
- Added two new command line interfaces. User can print out the default PythonTA configuration file in the command line using `python -m python_ta -g` and can specify the output format of the reporter using `python -m python_ta --output-format FILE`.
- Updated to Pylint v2.12. See "New checks" below for the new checkers enabled by default.
- Register ending location setter as pylint plugin.

### Bug fixes

- Fix bugs in `unnecessary-indexing` checker:
  1. False positive when the same loop variable is used in two loops in sequence.
  2. False negative when the loop variable can be simplified, but is also shadowed in the
     the loop body.
- Fix HTML report to link correctly to specific errors on the PythonTA documentation website.
- Fix bug when setting ending locations for `ClassDef`s that have no decorators.

### New checkers

Pylint checkers v2.12:

- `use-implicit-booleaness-not-len` (renamed from `len-as-condition`)

Pylint checkers v2.11:

- `consider-using-f-string`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

## [2.1.1] - 2021-09-23

### Bug fixes

- Fix HTML report to display file even when no errors are found.
- Fix pylint cache directory creation (backport of change from pylint 2.11)

## [2.1.0] - 2021-09-16

### Enhancements

- Added `line_end` and `column_end` to `JSONReporter` output.

## [2.0.0] - 2021-08-24

PythonTA's adopting semantic versioning as of this release, so we've bumped the version to 2.0.

### Enhancements

- Added basic CLI. Users can now run PythonTA in the command line either as a standalone
  script (`$ python_ta my_file`) or as a Python module (`$ python -m python_ta my_file`).
- Added new documentation website, hosted at <https://www.cs.toronto.edu/~david/pyta>.
- Added support for relative paths in `output` argument to `check_all`.
- Added new configuration option `pycodestyle-ignore` to customize the pycodestyle errors
  checked by `pep8-errors`.

### Changes

- Changed HTML report template to make it more user-friendly.
- Changed default HTML report output: by default now loads in a web browser without creating
  a temporary file (previously, `pyta_report.html`). This file can still be generated by passing
  `output='pyta_report.html'` to calls to `check_all`.
- Added new `output-format` option to specify reporter class.
- Changed API of PythonTA custom reporters.
- Updated to Pylint v2.10. See "New checks" below for the new checks enabled by default.
- Renamed `for-target-subscript` checker to `invalid-for-target`, and added support checking for
  loop targets that are attributes (e.g., `for obj.x in [1, 2, 3]`).
  ([#701](https://github.com/pyta-uoft/pyta/issues/701))

### Bug fixes

- Fixed bug with `python_ta.contracts`: do not check representation invariants
  when a helper method is called within an initializer.
- Fixed bug with `python_ta.contracts`: do not check class representation invariants in the
  initializer of a superclass.
- Fixed bug with `shadowing-in-comprehension` checker: do not treat `_` as a shadowed variable.
- Fixed bug with `unnecessary-indexing` checker: handle case where loop variable is first assigned
  before the for loop.
  ([#699](https://github.com/pyta-uoft/pyta/issues/699))
- Fixed bug where PythonTA would crash on files that used encodings other than UTF-8.
  PythonTA now reports an error and displays the invalid characters to the user.

### Deprecations

- Deprecated `pyta-reporter` option; use `output-format` instead.

### New checkers

Custom checkers:

- `missing-space-in-doctest`: Flag when a doctest prompt (`>>>`) is not followed by a space.
  E.g., `>>>my_function(1)`.

Pylint checkers v2.10:

- `forgotten-debug-statement`
- `format-string-without-interpolation`
- `use-dict-literal`
- `use-list-literal`

Pylint checkers v2.9:

- `consider-using-from-import`
- `unnecessary-dict-index-lookup`

Pylint checkers v2.8:

- `consider-using-with`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html).
Note that the above list only contains the Pylint checkers enabled by default in PythonTA.

### Internal

- Adopted semantic versioning.
- Created a Changelog.
- Added pre-commit hooks using pre-commit, black, isort, and prettier.
- Adopted Sphinx for documentation generation, using a Read the Docs template.
- Adopted `setup.cfg` file for configuration.
