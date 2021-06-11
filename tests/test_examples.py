import os
import os.path
import subprocess
import re
import pytest


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


def run_pylint_on_examples() -> dict[str, str]:
    """Return a dict mapping example file path to its pylint output
    """

    pylint_output = {}

    file_paths = get_file_paths()
    full_output = _get_full_pylint_output(file_paths)
    _, *individual_outputs = full_output.split("*************")
    for output, file_path in zip(individual_outputs, file_paths):
        _assert_parallel_output(output, file_path)
        pylint_output[file_path] = output

    return pylint_output


def _assert_parallel_output(output: str, file_path: str) -> None:
    """Assert that the output is for the given file"""
    file_base_name = os.path.basename(file_path)
    file_name, _ = os.path.splitext(file_base_name)
    assert file_name in output


def _get_full_pylint_output(file_paths: list[str]) -> str:

    output = subprocess.run(
        ['pylint', '--reports=n',
         '--rcfile=python_ta/.pylintrc',
         *file_paths],
        stderr=subprocess.STDOUT,
        stdout=subprocess.PIPE)

    return output.stdout.decode('UTF-8')


def create_checker(test_file, checker_name):
    """Creates a test function from a test file, and a checker name.
    test_file: The full path (string) to the file.
    checker_name: The hyphenated checker name that should be detected.
    An example of a valid checker_name would be: 'no-init-classes'
    """
    # The following are captured when this function is created.
    def new_test_func():
        found_pylint_message = False
        output = subprocess.run(
            ['pylint', '--reports=n',
             '--rcfile=python_ta/.pylintrc',
             test_file],
            stderr=subprocess.STDOUT,
            stdout=subprocess.PIPE)
        for line in output.stdout.decode('utf-8').split('\n'):
            if checker_name in line:
                found_pylint_message = True
                break
        if not found_pylint_message:
            print('Failed: ' + test_file)  # test doesn't say which file
        assert found_pylint_message
    return new_test_func


class TestExamples:
    # Private Attributes:
    #   - _pylint_outputs: mapping of file path to its pylint output

    _pylint_outputs: dict[str, str]

    @pytest.fixture(scope='session', autouse=True)
    def setup_pylint_output(self) -> None:
        """Run pylint on all the example files and map by file name"""
        TestExamples._pylint_outputs = run_pylint_on_examples()

    @pytest.mark.parametrize("test_file", get_file_paths())
    def test_examples_files(self, test_file):
        """Creates all the new unit tests dynamically from the testing directory."""
        base_name = os.path.basename(test_file)
        if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
            return
        if not base_name.lower().endswith('.py'):
            assert False
        checker_name = base_name[6:-3].replace('_', '-')  # Take off prefix and file extension.

        output = TestExamples._pylint_outputs[test_file]

        found_pylint_message = False
        for line in output.split("\n"):
            if checker_name in line:
                found_pylint_message = True
        if not found_pylint_message:
            print('Failed: ' + test_file)  # test doesn't say which file

        assert found_pylint_message
