from typing import Dict, Set

import os
import subprocess
import re
import pytest
import json
import itertools
from pylint import lint
from io import StringIO
import sys


_EXAMPLES_PATH = "examples/pylint/"
_EXAMPLE_PREFIX_REGEX = r"[CEFRW]\d{4}"


# The following tests appear to always fail (further investigation needed).
IGNORED_TESTS = [
    "e1131_unsupported_binary_operation.py",
    "e0118_used_prior_global_declaration.py",
    "w0125_using_constant_test.py",
    "w0631_undefined_loop_variable.py",
    "w1503_redundant_unittest_assert.py",
    "e1140_unhashable_dict_key.py",
    "r0401_cyclic_import.py",  # R0401 required an additional unit test but should be kept here.
]


def get_file_paths():
    """Gets all the files from the examples folder for testing. This will
    return all the full file paths to the file, meaning they will have the
    _EXAMPLES_PATH prefix followed by the file name for each element.
    A list of all the file paths will be returned."""
    test_files = []
    for _, _, files in os.walk(_EXAMPLES_PATH, topdown=True):
        for filename in files:
            if filename not in IGNORED_TESTS and filename.endswith(".py"):
                test_files.append(_EXAMPLES_PATH + filename)
    return test_files


@pytest.fixture(scope="session", autouse=True)
def symbols_by_file() -> Dict[str, Set[str]]:
    """Run pylint on all the example files and return the map of file name to the
    set of Pylint messages it raises."""

    sys.stdout = StringIO()
    lint.Run(
        [
            "--reports=n",
            "--rcfile=python_ta/config/.pylintrc",
            "--output-format=json",
            *get_file_paths()
        ], exit=False
    )
    jsons_output = sys.stdout.getvalue()
    sys.stdout = sys.__stdout__

    pylint_list_output = json.loads(jsons_output)

    file_to_symbol = {}
    for path, group in itertools.groupby(pylint_list_output, key=lambda d: d["path"]):
        symbols = {message["symbol"] for message in group}
        file = os.path.basename(path)

        file_to_symbol[file] = symbols

    return file_to_symbol


@pytest.mark.parametrize("test_file", get_file_paths())
def test_examples_files(test_file: str, symbols_by_file: Dict[str, Set[str]]) -> None:
    """Creates all the new unit tests dynamically from the testing directory."""
    base_name = os.path.basename(test_file)
    if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
        return
    if not base_name.lower().endswith(".py"):
        assert False
    checker_name = base_name[6:-3].replace("_", "-")  # Take off prefix and file extension.

    test_file_name = os.path.basename(test_file)
    file_symbols = symbols_by_file[test_file_name]

    found_pylint_message = checker_name in file_symbols
    assert found_pylint_message, f"Failed {test_file}. File does not add expected message."


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
            cyclic_import_helper, cyclic_import_file
        ], exit=False
    )
    jsons_output = sys.stdout.getvalue()
    sys.stdout = sys.__stdout__

    pylint_list_output = json.loads(jsons_output)

    found_cyclic_import = any(
        message["symbol"] == "cyclic-import" for message in pylint_list_output
    )
    assert found_cyclic_import, f"Failed {cyclic_import_file}. File does not add expected message."
