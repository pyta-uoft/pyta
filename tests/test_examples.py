import os
import os.path
import subprocess
import re


_EXAMPLES_PATH = 'examples/pylint/'
_EXAMPLE_PREFIX_REGEX = '[CEFRW]\d{4}'


# The following tests appear to always fail (further investigation needed).
IGNORED_TESTS = [
    'E1130_invalid_unary_operand_type.py',
    'E1131_unsupported_binary_operation.py',
    'W0222_signature_differs.py',
    'R0912_too_many_branches.py'
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
            print('Failed: ' + test_file)  # Nosetest doesn't say which file
        assert found_pylint_message
    return new_test_func


def test_examples_files():
    """Creates all the new unit tests dynamically from the testing directory."""
    for test_file in get_file_paths():
        base_name = os.path.basename(test_file)
        if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
            assert False
        if not base_name.lower().endswith('.py'):
            assert False
        checker_name = base_name[6:-3].replace('_', '-')  # Take off prefix and file extension.
        test_function = create_checker(test_file, checker_name)
        yield test_function
