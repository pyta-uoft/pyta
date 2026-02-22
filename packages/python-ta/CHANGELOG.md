# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### ✨ Enhancements

- Replaced the PyTA logo image data in the HTML report to be embedded directly in the src URL instead of using an external URL, and provided a favicon for the HTML report page using the same svg data.
- Extended `RecursionTable` to handle mutual recursion by taking in a list of function names to trace. Updated table output format correspondingly to include a "function" key column.
- Extended `unnecessary_f_string_checker.py` to present an alternate message when the input is already a string.
- Extended `snapshot_to_json` behaviour to handle `type` instances and display the `repr` of the type.

### 💫 New checkers

- `invalid-precondition-syntax`: Added new checker that checks if a function contains invalid syntax within its precondition statements.
- `invalid-postcondition-syntax`: Added new checker that checks if a function contains invalid syntax within its postcondition statements.

### 🐛 Bug fixes

- Fixed bug that allowed users to inject code into the browser template through the E9920 unnecessary f-string checker
- Fixed bug that caused user input containing markdown characters to be rendered by the markdown renderer in certain error messages

### 🔧 Internal changes

- Removed old documentation files under `python_ta/reporters/`
- Added tests for `infinite_loop_checker.py` to improve coverage for the `_name_holds_generator` function and the generator portion of the `_check_constant_loop_cond` function.
- Refactored `test_main.py` calls to use click's testing helpers.
- The `Z3Visitor`, `Z3Parser`, and `Z3ParseException` classes have been extracted into a _new Python package_, `python-ta-z3`.
- Removed extraneous `print` calls in `InfiniteLoopChecker`

## [2.12.1] - 2026-02-10

### 🐛 Bug fixes

- Fixed bug in `setendings.py` that raised an error when encountering a slice as part of a subscript tuple, e.g. `df.iloc[:, 0]`

## [2.12.0] - 2025-12-08

### ✨ Enhancements

- Updated `SnapshotTracer` to open the generated HTML report in a one-shot server, instead of opening the HTML file directly.
- Extended infinite-loop check to flag while loops whose conditions depend only on immutable variables and are not reassigned in the loop body.
- Added custom renderers for the PEP8 error codes: E204, E225, E231
- Added custom renderers for the PEP8 error codes: E271, E274, E502
- Updated the message format for Pycodestyle error messages to be more concise
- Added custom renderer for `line-too-long` to improve its error snippet to highlight the overflow segment instead of the entire line.
- Improved error message for error C0305 `trailing-newlines` and inserted a "DELETE" comment for each trailing newline.
- Added a solution to prevent possible large snippets created by the following errors: pylint error C0305, and pycodestyle errors E303, E304
- Added markdown rendering to display code in error messages
- Improved RI checking to raise a warning when a `NameError` is raised and the missing name matches an instance attribute, and is due to an omitted `self.` in the RI.
- Extended `AccumulationTable` class to support multiple loops in sequence within the same context manager
- Added a solution to prevent possible large snippets created by the `render_generic` function
- Support Python 3.14

### 💫 New checkers

Pylint checkers v4.0:

- `break-in-finally`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

Custom checkers:

- `unnecessary-f-string`: Added new checker that checks f-string to see if it only consists of a single bare format expression that can be replaced with the string representation of that expression
- `simplifiable-if`: Added a new checker that checks if an `if` or `elif` branch only contains a single nested `if` statement with a single branch.

### 🐛 Bug fixes

- Fixed issue that caused PEP8 errors E301, E302, E303, E304, E305 and E306 to not render properly

### 🔧 Internal changes

- Added tests for node_printers.py functions rendering the PEP8 error messages: E101, E116, E124, E128, E201, E202
- Added tests for node_printers.py functions rendering the following PEP8 error codes: E221, E251, E261, E272, E273, E302, E305, E306
- Refactored node_printers.py by grouping repeated code in helper functions and grouping identical functions into a single functions to reduce code duplication
- Updated GitHub Actions workflow to Node 24
- Refactored custom renderers to accept `config` parameter to stay consistent with the added parameter for `render-message`
- Refactored `setendings.py` to rely primarily on Astroid/Python’s built-in end-location attributes, reducing the amount of custom parsing logic
- Fixed `test_html_server.py` tests to be compatible with Windows
- Updated `conftest.py` and `test_black.py` to be compatible with pytest v9, removing usage of some deprecated features.
- Updated tests in `test_accumulation_table.py` to cover multi-loop behavior and added new cases
- Updated to pylint v4.0 and astroid v4.0

## [2.11.1] - 2025-08-17

### 🐛 Bug fixes

- Fixed reports to only include config files when they have errors
- Renamed the example `c2503_non_ascii_name.py` to `c2503_bad_file_encoding.py` to align with Pylint’s actual C2503 error identifier ("bad-file-encoding").
- Renamed the example `w0183_broad_exception_caught.py` to `w0718_broad_exception_caught.py` to align with Pylint’s actual error code for the given error identifier "broad-exception-caught" (W0718)
- Renamed `c0103_naming_convention_violation.py` to `c0103_invalid_name.py` to align with Pylint’s actual C0103 error identifier ("invalid-name").

## [2.11.0] - 2025-08-16

### ✨ Enhancements

- Support `x in` and `x not in` preconditions involving `set()`, `list()`, and `tuple()` function calls in the Z3 parser.
- Update the `output-format` configuration option to take reporter aliases rather than the plugin path.
- Integrated Watchdog to enable automatic re-checking of Python files when changes are detected.
- Added `autoformat-options` configuration option to let users specify command-line arguments to the Black formatting tool
- Update `check_all` and `check_error` functions to let users pass in `typing.IO` objects to the `output` argument
- Update the `forbidden-io-function-checker` to check functions from imported modules as well as methods (according to their qualified name)
- Update the `forbidden-io-function-checker` to flag aliases of forbidden functions
- Update how error messages are overridden such that section headers are no longer required within the config file
- Added `presistent_server` which recives the watch property changes through websockets and updates the HTML report
- Added optional `on_verify_fail` argument to `check_all` and `check_error`, allowing users to raise a `ValueError` and immediately stop execution when a file cannot be checked.
- Enhanced CFG generation to support `match` statements.
- Added the optional `format` argument to the `AccumulationTable` class, allowing users to select between csv or table formatted outputs.
- Added optional `z3_enabled` argument (default False) to `generate_cfg`, allowing users to enable `z3` functionalities and providing extra safeguard to prevent z3 (and z3 related) imports from being executed when z3 is not enabled.
- Added a dark mode toggle with system detection for the html reporter
- Replaced icons on the html reporter using the heroicons library, adding hover effects
- Extended `infinite-loop` check to flag while loops with constant conditions and no exit statements (e.g.: `return`, `break`, `raise`, `yield`, `sys.exit()`)
- Added command-line interface for CFG generation, allowing users to run `python -m python_ta.cfg <file>` with options for auto-open and visitor configuration
- Updated the color palette for the PythonTA web reporter to improve readability and visual hierarchy.
- Reduced shadow intensity, refined border opacity, and added subtle hover effects on interactive elements for the PythonTA web reporter to improve user experience.
- Aligned slider dropdown icons with the title text of errors in the web reporter to improve user experience
- Updated `SnapshotTracer` bundled webstepper version to v0.7.0
- Added a small margin to the topmost error instance card in the web reporter to prevent the top border from being cut off when the hover effect is activated
- Updated the error type text colors on the dark theme to be more consistent with that on the light theme
- Changed default MemoryViz version used by `snapshot` from "latest" to "0.7.0"

### 💫 New checkers

- `infinite-loop`: Provide an error message when a `while` loop never terminates, indicating an infinite loop.

### 🐛 Bug fixes

- Introduced the IDTracker class to track unique IDs in memory model diagrams across multiple snapshots.
- `check_contracts` no longer makes methods immediately enforce Representation Invariant checks when setting attributes of instances with the same type (one `Node` modifies another `Node` instance) and only checks RIs for these instances after the method returns.
- Fixed error in `contracts` where comments in docstring assertions are not removed while parsing
- Improved error message in `patches/transforms.py` where CFGVisitor is run
- Fixed a bug in AccumulationTable where loop variable names weren't being captured for all nested targets.
- Fixed a bug in the `infinite-loop` checker where function and method names were incorrectly included in the set of condition variables.
- Fixed "No Problems Detected" message colour in HTML report
- Fixed bug in `SnapshotTracer` output when using MemoryViz v0.7.0

### 🔧 Internal changes

- Refactored custom checker tests to group repeated tests using pytest.mark.parametrize.
- Dynamically loaded only the reporter specified in the configuration
- Added test case for `check_all` function ensuring proper behaviour when handling inputs in package notation.
- Improved `get_valid_files_to_check` function by removing unreachable code.
- Refactored `test_check.py` to use `pytest.mark.parametrize` annotation, improving test isolation and extracting inputs from test functions
- Added test case to `test_check.py` for better coverage of `colour_messages_by_type`
- Removed unused imports from `python_ta` module
- Wrapped type-only imports in if `TYPE_CHECKING` guards
- Refactored `render_pep8_errors` to use a dict that maps error codes to error functions instead of repeated conditional statements
- Added two test cases to `test_accumulation_table.py` to verify that `AccumulationTable` correctly extracts loop variables from nested tuple structures.
- Refactored `condition_logic_checker.py`, `cfg_generator.py` and `graph.py` by removing top-level `z3` (and z3 related) imports and moving them inside of functions where needed.
- Wrapped type-only `z3` (and z3 related) imports in a `TYPE_CHECKING` guard in `condition_logic_checker.py`, `graph.py` and `cfg_generator.py`.
- Added tests to improve coverage in `condition_logic_checker.py`, `graph.py` and `cfg_generator.py`, verifying behaviour in case of failed `z3` (and z3 related) import via import patching.
- Added `z3_enabled` optional initializer argument (default False) to `ControlFlowGraph` class in `graph.py` and `CFGVisitor` class in `visitor.py`.
- Updated `transforms.py` to ensure the patched version of `patch_ast_transforms` dynamically reads the `z3` option from linter config to reflect correct runtime setting.
- Simplified combined Z3 preconditions in `set_function_def_z3_constraints` using `z3.simplify`
- Refactored `one_shot_server` and `persistent_server` to allow for reuseablity.
- Removed old unused files
- Linked the contributions list (README.md) in the pull request template

## [2.10.1] - 2025-02-19

### 🐛 Bug fixes

- Fix import error when `graphviz` is not installed

## [2.10.0] - 2025-02-18

### ✨ Enhancements

- Added custom error message for `comparison-with-callable`
- Changed `pyta-template-file` argument to now resolve the file path relative to the CWD.
- Added a watch configuration option to the HTML reporter for persistent server mode.
- Added `server-port` configuration option to specify the port number to use when serving the PyTA HTML report.
- Added new checker option `mypy-options` in `static-type-checker` to let users override default mypy command-line arguments
- Added documentation for overriding messages
- Improved `check_contracts` error messages by ensuring a consistent format and phrasing
- Improved rendering of if/while/for syntax blocks in control flow graphs
- Ensured GraphViz-generated files have `.gv` extension
- Export `generate_cfg` from `python_ta.cfg`
- Move `check_all` configuration info to logging DEBUG level (was INFO)
- Update list of "error" checks
- Added optional boolean keyword arguments `argument_types`, `return_type`, `preconditions`, and `postconditions` to the `check_contracts` decorator, allowing users to selectively disable checks for functions

### 💫 New checkers

- `redundant-condition`: Provide error message when a conditional statement within a function is guaranteed true. This checker requires `z3` option to be turned on.
- `impossible-condition`: Provide error message when a conditional statement within a function is guaranteed false. This checker requires `z3` option to be turned on.
- `incompatible-argument-type`: Provide an error message when a function argument has an incompatible type.
- `incompatible-assignment`: Provide an error message when there is an incompatible assignment.
- `list-item-type-mismatch`: Provide an error message when a list item has an incompatible type.
- `unsupported-operand-types`: Provide an error message when an operation is attempted between incompatible types.
- `union-attr-error`: Provide an error message when accessing an attribute that may not exist on a Union type.
- `dict-item-type-mismatch`: Provide an error message when a dictionary entry has an incompatible key or value type.

### 🐛 Bug fixes

- Fixed issue in `static-type-checker` such that mypy no longer checks imported modules in the file being checked
- Fixed issue in `autoformat` where the default `max-line-length` value was not used
- Fixed issue in contract-checking `new_setattr` where an instance attribute was not always reset when reassigning it to an invalid value
- Fixed issue in `AccumulationTable` where accumulation expressions could not refer to loop variables
- Fixed issue in `snapshot` where some imported objects were being included in the output
- Fixed issue in `snapshot` where `None` was not being rendered in SVG correctly

### 🔧 Internal changes

- Configured CI tests to run on environments with and without `z3` dependency.
- Refactored `script.js` to avoid using jQuery, and instead use vanilla Javascript functionality.
- Configured CI to upload coverage report for both base and `z3` test environments
- Remove unnecessary calls to `node.stream()` in raw file checkers (pycodestyle and static type checkers)

## [2.9.2] - 2025-01-16

### 🐛 Bug fixes

- Ignore annotation-only assignment statements in `redundant-assignment` check

## [2.9.1] - 2024-12-09

### 🐛 Bug fixes

- Added `python_ta/debug/webstepper` to project `MANIFEST.in`

## [2.9.0] - 2024-12-09

### ✨ Enhancements

- Added `include_frames` filter to `snapshot`
- Added `exclude_frames` filter to `snapshot`
- Added `exclude_vars` filter to `snapshot`
- Added new `python_ta.debug` module with an `SnapshotTracer` context manager for generating memory models
- Added `z3` option to `inconsistent-or-missing-returns`, `redundant-assignment`, and `possibly-undefined` checkers to only check for feasible code blocks based on edge z3 constraints
- Included the name of redundant variable in `E9959 redundant-assignment` message
- Update to pylint v3.3 and and astroid v3.3. This added support for Python 3.13 and dropped support for Python 3.8. (No new checkers are enabled by default.)
- Added a STRICT_NUMERIC_TYPES configuration to `python_ta.contracts` allowing to enable/disable stricter type checking of numeric types
- Added integration with MemoryViz Webstepper
- Added `z3` option to `one-iteration-checker` to only check for feasible code blocks based on edge z3 constraints
- Added reporting for errors raised by custom transforms (`Z3Visitor`, `CFGVisitor`)
- Ensured `SnapshotTracer` does not include the `_trace_func` stack frame
- Enabled `SnapshotTracer` to create its `output_directory` argument if it doesn't already exist
- Changed `SnapshotTracer`'s Webstepper code line number to align with the source code line number

### 💫 New checkers

- `unmentioned-parameter`: Provide error message when a function parameter is not mentioned by name in the function's docstring. By default, this checker is disabled.

### 🐛 Bug fixes

- Fixed issue where `snapshot` errors on unserializable values
- Fixed issue within `Snapshot.py` where the `memory_viz_version` parameter was not respected
- Fixed issue where parallel assignment statements and assignment to multiple targets were not checked by `redundant_assignment_checker`
- Fixed issue where annotated assignment statements were not checked by `redundant_assignment_checker`
- Fixed issue where empty preconditions were preventing CFGs from being generated
- Added strict numeric type checking to enforce type distinctions across the entire numeric hierarchy, including complex numbers.
- Added strict type checking support for nested and union types (e.g., `list[int]`, `dict[float, int]`, `Union[int, float]`)
- Fixed issue where CFG edges from loop body to loop condition block was ignored during augmenting edge z3 constraints
- Fixed issue in `one-iteration-checker` where the message was not correctly reported for `while` loops when `z3` option is on
- Fixed crash when z3-solver is not installed
- Fixed crash when an inline comment had no spaces after the `#`

### 🔧 Internal changes

- Renamed `ExprWrapper` class to `Z3Parser`
- Renamed `ExprWrapper` module to `z3_parser` and moved it to new directory `python_ta.z3`
- Removed `node` attribute for `Z3Parser`
- Renamed `reduce` method of `Z3Parser` to `parse`
- Renamed `test_expr_wrapper` to `test_z3_parser`
- Added `is_feasible` attribute for `CFGEdge` and implemented update to edge feasibility based on lists of Z3 constraints
- Refactored codebase to use modern type annotations. Replaced `List` with `list`, `Dict` with `dict`, `Set` with `set`, and `Tuple` with `tuple`
- Checked for variable reassignment in `AugAssign` and `AnnAssign` node in parsing edge Z3 constraints
- Rendered logically infeasible control flow graph edges in light grey
- Modified `test_snapshot_to_json_sets_primitive` for Python 3.8 compatibility
- Added unit tests for `one_iteration_checker`
- Added mock `webbrowser.open` in tests to prevent browser tabs and HTTP requests during `python_ta.check_all()` executions.
- Added `pytest-mock` as a development dependency
- Make `test_snapshot.py::test_snapshot_serializes_unserializable_value` able to run on Windows.
- Added GitHub Action workflow for automatically publishing releases to PyPI
- Update `SnapshotTracer` tests to use `memory-viz@0.5.0` and prevent browser from opening
- Updated bundled webstepper version and removed source map, and excluded the bundle from prettier pre-commit check

## [2.8.1] - 2024-08-19

### 🐛 Bug fixes

- Fix loading of setendings plugin when z3-solver is not installed

## [2.8.0] - 2024-08-19

### ✨ Enhancements

- Add new boolean configuration `allow-local-imports` to allow for local imports
- Extended the `snasphot` function to include the relevant variables defined at the top level (global variables).
- Include the pycodestyle error code to the error message for PEP8 style errors
- Added date and time display to `PlainReporter` and `ColorReporter`
- Allowed specifying allowed names in configurations `allowed-import-modules` and `extra-imports` instead of just modules
- Improved error display for pycodestyle (E9989) errors E123, E203, E222, E226, and E262
- Added the configuration option to ignore naming convention violations (C9103 and C9104) for names matching the provided regular expression.
- Update to pylint v3.1 and and astroid v3.1
- Stored actual AST condition node in edges leading out of If/While blocks in generated control flow graphs.
- Stored valid Python function preconditions in initial edge to function code in generated function control flow graphs.
- Report warning when control flow graph creation encounters a syntax error related to control flow
- Added autoformat option that runs black formatting tool to python_ta.check_all()
- Extended the `snapshot` function to optionally generate a svg of the snapshot using MemoryViz when save parameter is true.

### 💫 New checkers

Pylint checkers v3.1:

- `use-yield-from`
- `deprecated-attribute`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

Custom checkers:

- `inconsistent-returns` and `missing-return-statement`: Provide clearer error messages when reporting missing return statements. This replaces pylint's [R1710](https://pylint.pycqa.org/en/latest/user_guide/messages/refactor/inconsistent-return-statements.html) check.

### 🐛 Bug fixes

- Fixed issue with error message of C0410 by reformating it to properly fit with the list of modules imported that are provided to it
- Fixed bug where `_` was marked as a built-in when running PythonTA after running doctest
- Fixed issue where annotated constant variable assignment was not considered as permissible top level code and triggered error E9992
- Fixed issue where top level class attribute assignment was considered as permissible top level code
- Fixed issue where `check_contracts` fails silently when function preconditions contain precondition violations, and when a representation invariant contains a call to a top-level function (not built-in or imported library).
- Fixed issue where methods called in representation invariants lead to infinite recursion.
- Fixed issue where `PossiblyUndefinedChecker` raised an error if the control flow graph was invalid due to syntax error

### 🔧 Internal changes

- Updated changelog and pull request template formats
- Added unit tests for PEP8 errors E115, E122, E125, E127, E129, E131 for `PycodestyleChecker`
- Added unit tests for PEP8 errors E223, E224, E227, E228, E265 for `PycodestyleChecker`
- Refactored `test_check_on_dir` in `test_check.py` module to test on `sample_dir`, a subset of `examples`
- Added unit test `test_examples_files_pyta` in `test_examples.py` to check every file in `examples` with PythonTA
- Added unit tests for PEP8 errors E266, E275, E301, E303, E304 for `PycodestyleChecker`
- Moved tests related to `__main__.py` from `test_check.py` to `test_main.py`
- Added more unit tests to `test_main.py` to increase coverage of `__main__.py` to 100%
- Updated `README.md` to reflect updated folder structure
- Added unit test `test_pycodestyle_errors_pyta` in `test_examples.py` to check every file in `e9989_pycodestyle` with PythonTA for PEP8 errors
- Parametrized tests for `PycodestyleChecker`
- Moved tests related to `snapshot.py` out of `test_accumulation_table.py` and into new module `test_snapshot.py`
- Updated GitHub Action tests to avoid running `test_accumulation_table.py` and `test_recursion_table.py` with coverage and add verbose output for debug testing
- Allowed GitHub Action tests to run on _all_ pull requests, including drafts
- Updated dependencies for GitHub Actions to use the latest versions
- Updated dependabot configuration to auto-update dependencies for GitHub Actions in the future
- Updated usage messages in `examples/sample_usage/` of `draw_cfg.py` and `print_ast.py` to be accurate on all operating systems
- Removed redundant line from `tests/test_examples.py`
- Fixed minor typo in an error message in `python_ta/cfg/visitor.py`
- Updated `ExprWrapper` to support `set/list/tuple` literals and `in/not in` operators
- Updated `snapshot.py` and `test_snapshot.py` to align with MemoryViz 0.2.0 updates
- Updated `ExprWrapper` to support string variables and `==`, `in/not in`, indexing and slicing operators
- Added protected `_z3_vars` attribute to `ControlFlowGraph` to store variables to be used in Z3 solver
- Removed unused imports from `python_ta/cfg/graph.py`
- Extended functionality of `ExprWrapper` class to include function definitions' arguments and name assignments
- Added `z3` to dependencies installed as part of the `docs` job in the GitHub Actions workflow
- Added tests to maintain/increase coverage of `visitor.py`, `graph.py`, and `ExprWrapper.py`
- Removed deprecated and redundant `future` argument from `node.frame()` call in `invalid_name_checker.py`
- Updated pylint to v3.2.6 and astroid to v3.2.4 (no new checks were enabled by default)
- Excluded `node_modules/` folder from package autodiscovery
- Updated `graph.py` to augment control flow graph edges with z3 constraints
- Added support for the `!=` operator and replaced dictionary indexing with `.get` in `ExprWrapper`.
- Refactored `Z3Visitor` to use `safe_infer()` instead of `inferred()` and added handling of `AstroidError`.
- Add `negate` attribute to `CFGEdge`

## [2.7.0] - 2023-12-14

### ✨ Enhancements

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

### 🐛 Bug fixes

- Fix bug in ending location setting for `Attribute` and `DelAttr` nodes when the same attribute
  was accessed twice on the same line.
- Fix bug where the `naming-convention-violation` checker was checking variables defined in a module's main block. This was inconsistent with the `forbidden-global-variables` checker.
- Fixed bug with `invalid-range-index`: do not attempt any inference of variables in `range` expressions. All range arguments involving variables will be ignored by this checker.

### 💫 New checkers

Pylint checkers v3.0:

- `invalid-field-call`
- `return-in-finally`
- `kwarg-superseded-by-positional-arg`
- `unnecessary-negation` (renamed from `unneeded-not`)

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

### 🔧 Internal changes

- Remove experimental type inference code.

## [2.6.4] - 2023-11-10

### 🐛 Bug fixes

- Fixed bug with `invalid-range-index` when variables are used in `range` expressions.

## [2.6.3] - 2023-10-09

### 🐛 Bug fixes

- Ensure pycodestyle W503, line break before binary operator, is disabled (regression from 2.6.2).
- Fix `check_contracts` typings so PyCharm static checking will work
- Fix `invalid-range-index` bug where valid range calls were flagged as invalid

## [2.6.2] - 2023-09-22

### 🐛 Bug fixes

- Fix `naming-convention-violation` bug where `_` was considered an invalid variable name.
- Fix `naming-convention-violation` bug where top-level constants were being checked as regular variable names.

### ✨ Enhancements

- Created many custom renderers to make the code snippets for `pep8-errors` easier to understand.

## [2.6.1] - 2023-08-13

### 🐛 Bug fixes

- Make `graphviz` an optional dependency, and clarify the installation requirements for visualizing
  control flow graphs.
- Fix `check_contrats` handling of forward references in class type annotations when using `check_contracts` decorator.
- Fix handling of `|` in type annotations (by updating to `typeguard` v4.1.0).

## [2.6.0] - 2023-08-06

### ✨ Enhancements

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

### 🐛 Bug fixes

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

### 💫 New checkers

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

### 🐛 Bug fixes

- Fixed bug in possibly-undefined checker where a comprehension variable is falsely flagged as possibly undefined.
- Fixed bug where `check_errors` and `check_all` opens a webpage when a nonexistent or unreadable path is passed as an argument.
- Fixed the CFG implementation to resolve a bug in the possibly-undefined checker where variables were falsely flagged as possibly undefined when the code conditionally raises an exception and the variable was referenced afterwards.
- Fixed bug where the generated CFGs will highlight the except block as unreachable if the same exception it is handling was raised in the body of the tryexcept.

### 💫 New checkers

Custom checkers:

- `forbidden-python-syntax`: Flag code that is not permitted to be used on an assessment.

### 🔧 Internal changes

- Pin dependency versions

## [2.4.2] - 2023-1-31

### 🐛 Bug fixes

- Fixed custom message formats based on Pylint 2.15 updates.
- Fixed bug in shadowing-in-comprehension checker when target is a subscript node.
- Ensured `check_contracts` and `check_all_contracts` do nothing when `ENABLE_CONTRACT_CHECKING` is `False`.

## [2.4.1] - 2023-1-13

### 🐛 Bug fixes

- Fixed PyTA contract checking for method calls when running modules in PyCharm using the "Run File in Python Console" action.

## [2.4.0] - 2022-12-21

### ✨ Enhancements

- `unnecessary_indexing_checker` has now been extended to check comprehensions in addition to for loops.
- `invalid_for_target_checker` has now been extended to check comprehensions in addition to for loops.
- `forbidden_io_function_checker` is now able to check for calls to IO functions written at the top-level of a module, but outside the main block.
- `python_ta.debug.AccumulationTable` is extended to support printing loop iterations for while loops.
- Violated representation invariant error message now includes the class name and current values of the instance attributes.
- Added constant `python_ta.contracts.ENABLE_CONTRACT_CHECKING` to only check contracts when its value is set to `True`.
- `python_ta.debug.AccumulationTable` has extended loop detection to allow the loop to appear anywhere inside the with statement.

### 🐛 Bug fixes

- Fixed Issue #831: Contract Checker Bug. Now raises `AssertionError` when the expected type is `float` but got `int` instead.
- PyTA contracts' type checking now raises `AssertionError` when the expected type is `int` but got `bool` instead.
- Fixed PyTA contract checking when running modules in PyCharm using the "Run File in Python Console" action.

### 💫 New checkers

Custom checkers:

- `forbidden-top-level-code`: Flag code written at the top level when it is not one of the four acceptable types.

## [2.3.3] - 2022-09-05

### 🐛 Bug fixes

- Restored 'line_end', 'column_end', and 'snippet' fields in JSON reporter output.

## [2.3.2] - 2022-08-30

### 🐛 Bug fixes

- Updated jsonreporter to get data from the new pylint Message class (#840)

### 🥽 Experimental

- Added preliminary support for translation of constraints into Z3 solver.
  (This is currently not enabled by default in PythonTA.)

## [2.3.1] - 2022-08-08

### 🐛 Bug fixes

- Add missing `toml` package to library dependencies.
- Improve formatting of `None` and `float`s in `AccumulationTable` display.
  Also make minor improvements to the documentation.

## [2.3.0] - 2022-08-08

### ✨ Enhancements

- Added new command line argument `-v/--version`. User can print out current PythonTA version using `python -m python_ta -v`.
- Preconditions, postconditions, and representation invariants are now parsed only once and compiled.
- Can configure custom error messages for pylint in a toml file.
- `missing_space_in_doctest_checker` is now able to check doctests in python modules and classes.
- Updated to Pylint v2.14. See "New checks" below for the new checkers enabled by default.
- Added new `python_ta.debug` module with an `AccumulationTable` context manager for loop print debugging.
- Improve message for R1710 (inconsistent-return-statements)

### 🐛 Bug fixes

- Function `check_all_contracts` skips contract checks for functions and classes which are not defined in a module whose name is passed as an argument. If `decorate_main` argument is `True`, functions and classes defined in `__main__` module will be checked without needing to pass in additional arguments.

### 💫 New checkers

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

### ✨ Enhancements

- Added support for postconditions in function docstring.
- Improve error message of `unncessary-indexing` checker.
- Added CLI for `python_ta.contracts` module for executing a file with contract checking
  (`$ python -m python_ta.contracts FILE`)
- Added two new command line interfaces. User can print out the default PythonTA configuration file in the command line using `python -m python_ta -g` and can specify the output format of the reporter using `python -m python_ta --output-format FILE`.
- Updated to Pylint v2.12. See "New checks" below for the new checkers enabled by default.
- Register ending location setter as pylint plugin.

### 🐛 Bug fixes

- Fix bugs in `unnecessary-indexing` checker:
  1. False positive when the same loop variable is used in two loops in sequence.
  2. False negative when the loop variable can be simplified, but is also shadowed in the
     the loop body.
- Fix HTML report to link correctly to specific errors on the PythonTA documentation website.
- Fix bug when setting ending locations for `ClassDef`s that have no decorators.

### 💫 New checkers

Pylint checkers v2.12:

- `use-implicit-booleaness-not-len` (renamed from `len-as-condition`)

Pylint checkers v2.11:

- `consider-using-f-string`

For more information on these checkers, please see the
[Pylint release notes](http://pylint.pycqa.org/en/latest/whatsnew/index.html). Note that the above
list only contains the Pylint checkers enabled by default in PythonTA.

## [2.1.1] - 2021-09-23

### 🐛 Bug fixes

- Fix HTML report to display file even when no errors are found.
- Fix pylint cache directory creation (backport of change from pylint 2.11)

## [2.1.0] - 2021-09-16

### ✨ Enhancements

- Added `line_end` and `column_end` to `JSONReporter` output.

## [2.0.0] - 2021-08-24

PythonTA's adopting semantic versioning as of this release, so we've bumped the version to 2.0.

### ✨ Enhancements

- Added basic CLI. Users can now run PythonTA in the command line either as a standalone
  script (`$ python_ta my_file`) or as a Python module (`$ python -m python_ta my_file`).
- Added new documentation website, hosted at <https://www.cs.toronto.edu/~david/pyta>.
- Added support for relative paths in `output` argument to `check_all`.
- Added new configuration option `pycodestyle-ignore` to customize the pycodestyle errors
  checked by `pep8-errors`.

### ✨ Changes

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

### 🐛 Bug fixes

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

### 🚧 Deprecations

- Deprecated `pyta-reporter` option; use `output-format` instead.

### 💫 New checkers

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

### 🔧 Internal changes

- Adopted semantic versioning.
- Created a Changelog.
- Added pre-commit hooks using pre-commit, black, isort, and prettier.
- Adopted Sphinx for documentation generation, using a Read the Docs template.
- Adopted `setup.cfg` file for configuration.
