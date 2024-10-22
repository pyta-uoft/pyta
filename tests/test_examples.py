from __future__ import annotations

import itertools
import json
import os
import re
import sys
from io import StringIO
from typing import Union

import pytest
from pylint import lint

import python_ta

_EXAMPLES_PATH = "examples/pylint/"
_CUSTOM_CHECKER_PATH = "examples/custom_checkers/"
_PYCODESTYLE_PATH = "examples/custom_checkers/e9989_pycodestyle/"

_EXAMPLE_PREFIX_REGEX = r"[cerfw]\d{4}"
_PYCODESTYLE_PREFIX_REGEX = r"^e\d{3}_(error|no_error)\.py$"


# The following tests appear to always fail (further investigation needed).
IGNORED_TESTS = [
    "e1131_unsupported_binary_operation.py",
    "e0118_used_prior_global_declaration.py",
    "w0631_undefined_loop_variable.py",
    "w1503_redundant_unittest_assert.py",
    "e1140_unhashable_dict_key.py",
    "r0401_cyclic_import.py",  # R0401 required an additional unit test but should be kept here.
    "e9999_forbidden_import_local.py",  # This file itself (as an empty file) should not be tested
    "c9104_ModuleNameViolation.py",  # Due to different naming format, this file is handled separately
    "e0643_potential_index_error.py",
    "e1003_bad_super_call.py",
    "e1143_unhashable_member.py",
    "r0201_no_self_use.py",
    "e9950_forbidden_python_syntax.py",
]


def get_file_paths(paths: Union[str, list[str]]) -> list[str]:
    """
    Get all the Python files from the specified directories for testing. This will
    return the full file paths for each Python file, excluding those listed in IGNORED_TESTS.
    The file paths will have the directory path prefixed to the file name for each element.
    A list of all the file paths will be returned.

    :param paths: The path or list of paths to retrieve the Python files from.
    :return: A list of full file paths to the Python files.
    """
    test_files = []

    if isinstance(paths, str):
        paths = [paths]

    for path in paths:
        for root, _, files in os.walk(path, topdown=True):
            for filename in files:
                if filename not in IGNORED_TESTS and filename.endswith(".py"):
                    full_path = os.path.join(root, filename)
                    rel_path = os.path.relpath(full_path, path)
                    test_files.append(os.path.join(path, rel_path))

    return test_files


def _symbols_by_file_pyta(paths: list[str], include_msg: bool = False) -> dict[str, set[str]]:
    """
    Run python_ta.check_all() on files from specified directories and return the map of file name to the
    set of PythonTA messages it raises. If include_msg is set True, PythonTA message descriptions are
    included along with message symbols.

    :param paths: The paths to retrieve the files from.
    :param include_msg: whether to include message descriptions in the symbol set
    :return: A dictionary mapping each file name to a set of PythonTA message symbols
    (and descriptions if include_msg is True).
    """
    sys.stdout = StringIO()
    python_ta.check_all(
        module_name=get_file_paths(paths),
        config={
            "output-format": "python_ta.reporters.JSONReporter",
            "enable": ["C9960"],
        },
    )

    jsons_output = sys.stdout.getvalue()
    sys.stdout = sys.__stdout__
    pyta_list_output = json.loads(jsons_output)

    file_to_symbol = {}
    for path, group in itertools.groupby(
        pyta_list_output, key=lambda d: os.path.basename(d["filename"])
    ):
        symbols = set()
        for message in group:
            for msg in message["msgs"]:
                symbols.add(msg["symbol"])
                if include_msg:
                    symbols.add(msg["msg"])

        file = os.path.basename(path)
        file_to_symbol[file] = symbols

    return file_to_symbol


@pytest.fixture(scope="session")
def pyta_examples_symbols() -> dict[str, set[str]]:
    """
    A pytest fixture that runs once per test session.
    This fixture analyzes example files using python_ta and returns a dictionary mapping each file name
    to the set of PythonTA message symbols raised.

    :return: A dictionary mapping file names to sets of PythonTA message symbols.
    """
    return _symbols_by_file_pyta([_EXAMPLES_PATH, _CUSTOM_CHECKER_PATH])


@pytest.fixture(scope="session")
def pyta_pycodestyle_symbols() -> dict[str, set[str]]:
    """
    A pytest fixture that runs once per test session.
    This fixture analyzes pycodestyle error test cases using python_ta and returns a dictionary mapping each file name
    to the set of PythonTA message symbols and descriptions.

    :return: A dictionary mapping file names to sets of PythonTA message symbols and descriptions.
    """
    return _symbols_by_file_pyta([_PYCODESTYLE_PATH], include_msg=True)


@pytest.mark.parametrize("test_file", get_file_paths([_EXAMPLES_PATH, _CUSTOM_CHECKER_PATH]))
def test_examples_files_pyta(test_file: str, pyta_examples_symbols: dict[str, set[str]]) -> None:
    """
    Dynamically creates and runs unit tests for Python files in the examples and custom checker directories.
    This test function deduces the error type from the file name and checks if the expected error message is present
    in PythonTA's report.
    """
    base_name = os.path.basename(test_file)
    if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
        return
    if not base_name.lower().endswith(".py"):
        assert False
    checker_name = base_name[6:-3].replace("_", "-")  # Take off prefix and file extension.

    file_symbols = pyta_examples_symbols[base_name]

    found_pylint_message = checker_name in file_symbols
    assert (
        found_pylint_message
    ), f"Failed {test_file}. File does not add expected message  {file_symbols}."


@pytest.mark.parametrize("test_file", get_file_paths(_PYCODESTYLE_PATH))
def test_pycodestyle_errors_pyta(
    test_file: str, pyta_pycodestyle_symbols: dict[str, set[str]]
) -> None:
    """
    Dynamically creates and runs unit tests for pycodestyle error test cases.
    This test function deduces the PEP8 error code from the file names. It checks if pycodestyle error is present
    in PythonTA's report and if the correct PEP8 error type is in the message description.
    """
    base_name = os.path.basename(test_file)
    if not re.match(_PYCODESTYLE_PREFIX_REGEX, base_name.lower()):
        return
    if not base_name.lower().endswith(".py"):
        assert False

    # skip the test case if it does not have errors
    has_error = base_name[5:] == "error.py"
    if not has_error:
        return

    error_code = base_name[:4].upper()  # get the specific PEP8 error code
    test_file_name = os.path.basename(test_file)
    file_symbols = pyta_pycodestyle_symbols[test_file_name]

    found_pycodestyle_message = "pep8-errors" in file_symbols
    assert found_pycodestyle_message, f"Failed {test_file}. File does not add expected message."
    assert any(
        error_code in msg for msg in file_symbols
    ), f"Failed {test_file}. The correct PEP8 error type is not in reported message."


def test_c9104_module_name_violation() -> None:
    """
    Test that examples/custom_checkers/c9104_ModuleNameViolation.py adds C9104 module-name-violation.
    This test is separate as the naming convention for this file is different from the rest of the examples.
    """
    module_name_violation = "examples/custom_checkers/c9104_ModuleNameViolation.py"
    sys.stdout = StringIO()
    python_ta.check_all(
        module_name=module_name_violation,
        config={
            "output-format": "python_ta.reporters.JSONReporter",
        },
    )

    jsons_output = sys.stdout.getvalue()
    sys.stdout = sys.__stdout__
    pyta_list_output = json.loads(jsons_output)

    message_symbols = []
    for message in pyta_list_output:
        for msg in message["msgs"]:
            message_symbols.append(msg["symbol"])

    found_module_name_violation = "module-name-violation" in message_symbols
    assert (
        found_module_name_violation
    ), f"Failed {module_name_violation}. File does not add expected message."


def test_cyclic_import() -> None:
    """Test that examples/pylint/R0401_cyclic_import adds R0401 cyclic-import.

    Reason for creating a separate test:
    This test is separate as pylint adds the R0401 message to the final module within
    the batch of given modules, not to the R0401_cyclic_import or cyclic_import_helper.
    It is unintuitive to force R0401_cyclic_import to be the final batched module so that
    the parametrized test suite passes, so cyclic-import is ignored in the paramterized suite
    and this additional test is created on the side.
    """

    cyclic_import_helper = "examples/pylint/cyclic_import_helper.py"
    cyclic_import_file = "examples/pylint/r0401_cyclic_import.py"

    sys.stdout = StringIO()
    lint.Run(
        [
            "--reports=n",
            "--rcfile=python_ta/config/.pylintrc",
            "--output-format=json",
            cyclic_import_helper,
            cyclic_import_file,
        ],
        exit=False,
    )
    jsons_output = sys.stdout.getvalue()
    sys.stdout = sys.__stdout__

    pylint_list_output = json.loads(jsons_output)

    found_cyclic_import = any(
        message["symbol"] == "cyclic-import" for message in pylint_list_output
    )
    assert found_cyclic_import, f"Failed {cyclic_import_file}. File does not add expected message."
