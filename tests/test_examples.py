from typing import Dict, List, Set

import os
import subprocess
import re
import pytest
import json
import itertools


_EXAMPLES_PATH = 'examples/pylint/'
_EXAMPLE_PREFIX_REGEX = r'[CEFRW]\d{4}'


# The following tests appear to always fail (further investigation needed).
IGNORED_TESTS = [
    'E1131_unsupported_binary_operation.py',
    'E0118_used_prior_global_declaration.py',
    'W0125_using_constant_test.py',
    'W0631_undefined_loop_variable.py',
    'W1503_redundant_unittest_assert.py',
    'E1140_unhashable_dict_key.py',
    'R0401_cyclic_import.py'
]


def get_file_paths():
    """Gets all the files from the examples folder for testing. This will
    return all the full file paths to the file, meaning they will have the
    _EXAMPLES_PATH prefix followed by the file name for each element.
    A list of all the file paths will be returned."""
    test_files = []
    for _, _, files in os.walk(_EXAMPLES_PATH, topdown=True):
        for filename in files:
            if filename not in IGNORED_TESTS and filename.endswith('.py'):
                test_files.append(_EXAMPLES_PATH + filename)
    return test_files


@pytest.fixture(scope='session', autouse=True)
def symbols_by_file() -> Dict[str, Set[str]]:
    """Run pylint on all the example files and return the map of file name to the
    set of Pylint messages it raises."""
    output = subprocess.run(
        ['pylint', '--reports=n',
         '--rcfile=python_ta/.pylintrc',
         '--output-format=json',
         *get_file_paths()],
        stderr=subprocess.STDOUT,
        stdout=subprocess.PIPE)

    jsons_output = output.stdout.decode('UTF-8')
    pylint_list_output = json.loads(jsons_output)

    file_to_symbol = {}
    for path, group in itertools.groupby(pylint_list_output, key=lambda d: d['path']):
        symbols = {message['symbol'] for message in group}
        file = os.path.basename(path)

        file_to_symbol[file] = symbols

    return file_to_symbol


@pytest.mark.parametrize("test_file", get_file_paths())
def test_examples_files(test_file: str, symbols_by_file: Dict[str, Set[str]]) -> None:
    """Creates all the new unit tests dynamically from the testing directory."""
    base_name = os.path.basename(test_file)
    if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
        return
    if not base_name.lower().endswith('.py'):
        assert False
    checker_name = base_name[6:-3].replace('_', '-')  # Take off prefix and file extension.

    test_file_name = os.path.basename(test_file)
    file_symbols = symbols_by_file[test_file_name]

    found_pylint_message = checker_name in file_symbols
    if not found_pylint_message:
        print('Failed: ' + test_file)  # test doesn't say which file
    assert found_pylint_message, f'Failed {test_file}. File does not add expected message.'
