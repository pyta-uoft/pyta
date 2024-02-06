# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

- Add new boolean configuration `allow-local-imports` to allow for local imports

### Enhancements

- Include the pycodestyle error code to the error message for PEP8 style errors
- Added date and time display to `PlainReporter` and `ColorReporter`

## [2.7.0] - 2024-12-14

### Enhancements

- Added new configuration option `use-pyta-error-messages` to let users choose whether PythonTA should overwrite pylint's error messages.
- Both PlainReporter and ColorReporter emphasize specific code chunks by using overline characters under any part that is highlighted as ERROR.
- Added snapshot function for deriving a list of dictionaries containing local variables from relevant functions and/or stack frames.
- Added new configuration option `allow-pylint-comments` to let users choose whether PythonTA should allow comments beginning with pylint: or not.
- `AccumulationTable` can now track variables initialized within the `for` loop. Prior, only variables initialized before the `for` loop could be tracked.
- `AccumulationTable` now stores deep copies of objects rather than shallow copies, thus fixing issues that come up in case of mutation during loop.
- `AccumulationTable` can now take in any accumulator expressions, for eg. `x * 2`, instead of just variables.
- `AccumulationTable` now has an optional initialization argument `output` which allows the users to choose whether they want to write the Accumulation Table to a file.
- Created a `RecursionTable` context manager for recursive tracing using a tabular output.
- Support Python 3.12 (requiring upgrade to pylint and astroid 3.0)

### Bug fixes

- Fix bug in ending location setting for `Attribute` and `DelAttr` nodes when the same attribute
  was accessed twice on the same line.
- Fix bug where the `naming-convention-violation` checker was checking variables defined in a module's main block. This was inconsistent with the `forbidden-global-variables` checker.
- Fixed bug with `invalid-range-index`: do not attempt any inference of variables in `range` expressions. All range arguments involving variables will be ignored by this checker.

### New checkers

Pylint checkers v3.0:

- `invalid-field-call`
- `return-in-finally`
- `kwarg-superseded-by-positional-arg`
- `unnecessary-negation` (renamed from `unneeded-not`)

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

### Internal

- Remove experimental type inference code.

## [2.6.4] - 2024-11-10

### Bug fixes

- Fixed bug with `invalid-range-index` when variables are used in `range` expressions.

## [2.6.3] - 2023-10-09

### Bug fixes

- Ensure pycodestyle W503, line break before binary operator, is disabled (regression from 2.6.2).
- Fix `check_contracts` typings so PyCharm static checking will work
- Fix `invalid-range-index` bug where valid range calls were flagged as invalid

## [2.6.2] - 2023-09-22

### Bug fixes

- Fix `naming-convention-violation` bug where `_` was considered an invalid variable name.
- Fix `naming-convention-violation` bug where top-level constants were being checked as regular variable names.

### Enhancements

- Created many custom renderers to make the code snippets for `pep8-errors` easier to understand.

## [2.6.1] - 2023-08-13

### Bug fixes

- Make `graphviz` an optional dependency, and clarify the installation requirements for visualizing
  control flow graphs.
- Fix `check_contrats` handling of forward references in class type annotations when using `check_contracts` decorator.
- Fix handling of `|` in type annotations (by updating to `typeguard` v4.1.0).

## [2.6.0] - 2023-08-06

### Enhancements

- Can now create control flow graphs using `python_ta.control_flow_graphs` to visualize the
  execution paths of Python code.
- `forbidden-top-level-code` and `forbidden-global-variables` now allow top-level type alias
  assignment statements.
- The `trailing-whitespace` error message now highlights the trailing whitespace.
- The `unnecessary-indexing` error now checks for a greater variety of loop/comprehension indexes.
- Provided configuration files are now merged with PythonTA defaults, so you now only
  need to specify options that you want to be overridden. To ignore PythonTA defaults (the
  old behaviour), pass `load_default_config=False` to `check_errors` and `check_all`.
- Improved the code snippets for the `pep8-errors` "blank line" messages.
  Extra blank lines are now highlighted, and suggestions are added when blank lines are missing.
- The default value of the `pyta-number-of-messages` configuration option is now 0 (changed from 5).
  This causes all error occurrences to be displayed.
- Improved efficiency of the contract-checking custom `setattr` for classes.
- Added new function `python_ta.contracts.validate_invariants` to manually check contracts
  for an object.
- Updated to [pycodestyle v2.11](https://github.com/PyCQA/pycodestyle/blob/main/CHANGES.txt).

### Bug Fixes

- Fixed bug where running `python3 -m python_ta --generate-config` yields a `FileNotFoundError`.
- Fixed bug in how PythonTA reports error messages that occur when parsing configuration files.
- Ensured some config file parsing errors no longer display incorrect lines in the error report.
- Fixed bug where the `HTMLReporter` and `JSONReporter` would ignore the `pyta-number-of-messages`
  option and always display all error occurrences.
- Fixed bug in `check_contracts` where imported classes were not correctly resolved when checking
  types.
- Fixed bug for class contract-checking when assigning an instance attribute that violates a class
  type constraint or representation invariant. Previously, the instance attribute changed to the
  new value after the error was raised, but now is correctly restored to the original value.
- Remove line double-spacing in PlainReporter and ColorReporter output code snippets.

### New checkers

Custom checkers:

- `invalid-name-checker`: Provide beginner-friendly error messages when reporting variable names
  that violate Python naming conventions. This replaces pylint's
  [C0103](https://pylint.pycqa.org/en/latest/user_guide/messages/convention/invalid-name.html)
  check.

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
