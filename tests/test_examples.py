from typing import Dict, List, Set

import os
import os.path
import subprocess
import re
import pytest
import json


_EXAMPLES_PATH = 'examples/pylint/'
_EXAMPLE_PREFIX_REGEX = '[CEFRW]\d{4}'


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


def _get_full_pylint_json_output() -> List[Dict]:
    output = subprocess.run(
        ['pylint', '--reports=n',
         '--rcfile=python_ta/.pylintrc',
         '--output-format=json',
         *get_file_paths()],
        stderr=subprocess.STDOUT,
        stdout=subprocess.PIPE)

    jsons_output = output.stdout.decode('UTF-8')
    jsons_output = _strip_trailing_asni(jsons_output)
    return json.loads(jsons_output)


def _strip_trailing_asni(str_to_strip: str) -> str:
    """Return the string stripped to the final ']'

    Running Pytest from a Python Console produces a trailing ANSI '\x1b[0m' code whereas
    the CLI Pytest does not.
    """
    trailing_token = str_to_strip.split(']')[-1]
    return str_to_strip[:-len(trailing_token)]


def _compile_message_symbols_per_file(pylint_output_list: List[Dict]) -> Dict[str, Set[str]]:
    """Return a dict mapping file name to the set of Pylint message symbols it raises.

    The file name is the basename, not the full or relative path
    (this is to avoid being unable to access a value because of \\ and / paths)
    """
    symbols_by_file = {}

    for pylint_message_data in pylint_output_list:
        file_name = os.path.basename(pylint_message_data['path'])
        symbol = pylint_message_data['symbol']

        if file_name not in symbols_by_file:
            symbols_by_file[file_name] = set()

        symbols_by_file[file_name].add(symbol)

    return symbols_by_file


@pytest.fixture(scope='session', autouse=True)
def symbols_by_file() -> Dict[str, Set[str]]:
    """Run pylint on all the example files return the map of file name to the
    set of Pylint messages it raises."""
    pylint_list_output = _get_full_pylint_json_output()
    return _compile_message_symbols_per_file(pylint_list_output)


@pytest.mark.parametrize("test_file", get_file_paths())
def test_examples_files(test_file: str, symbols_by_file: Dict[str, Set[str]]):
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
    assert found_pylint_message
