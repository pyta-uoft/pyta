# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

## [2.3.3] - 2022-09-05

### Bug fixes

- Restored 'line_end', 'column_end', and 'snippet' fields in JSON reporter output.

### Enhancements

- `forbidden_io_function_checker` is now able to check for calls to IO functions written at the top-level of a module, but ouside of the main block.

### New checkers

Custom checkers:

- `top_level_code`: Flag code written at the top level when it is not one of the four acceptable types.

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
