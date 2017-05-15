"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import python_ta
> python_ta.check_all('mymodule')

Or, put the following code in your Python module:

if __name__ == '__main__':
    import python_ta
    python_ta.check_all()
"""
import importlib.util
import os
import sys
import tokenize
import webbrowser

import pylint.lint as lint
import pylint.utils as utils
import pylint

from astroid import MANAGER
from astroid import modutils

from .reporters import ColorReporter
from .patches import patch_all

# Local version of website; will be updated later.
HELP_URL = 'http://www.cs.toronto.edu/~david/pyta/'


# check the python version
if sys.version_info < (3, 4, 0):
    print('You need Python 3.4 or later to run this script')


def check_errors(module_name='', reporter=ColorReporter, number_of_messages=5,
                 config=''):
    """Check a module for errors, printing a report.
    """
    _check(module_name=module_name, reporter=reporter, number_of_messages=number_of_messages, level='error', local_config=config)


def check_all(module_name='', reporter=ColorReporter, number_of_messages=5,
              config=''):
    """Check a module for errors and style warnings, printing a report."""
    _check(module_name, reporter, number_of_messages, level='all',
           local_config=config)


def _load_pylint_plugins(current_reporter, local_config, pep8):
    """Register checker plugins for pylint. Return linter."""
    linter = lint.PyLinter(reporter=current_reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['python_ta/checkers/forbidden_import_checker',
                                'python_ta/checkers/global_variables_checker',
                                'python_ta/checkers/dynamic_execution_checker',
                                'python_ta/checkers/IO_Function_checker',
                                # TODO: Fix this test
                                #'python_ta/checkers/invalid_range_index_checker',
                                'python_ta/checkers/assigning_to_self_checker',
                                'python_ta/checkers/always_returning_checker',
                                'python_ta/checkers/type_inference_checker'])
    if pep8:
        linter.load_plugin_modules(['python_ta/checkers/pycodestyle_checker'])

    if isinstance(local_config, str) and local_config != '':
        # Use config file at the specified path instead of the default.
        linter.read_config_file(local_config)
    else:
        # Use default config file in the python_ta package.
        linter.read_config_file(os.path.join(os.path.dirname(__file__), '.pylintrc'))

        # Override part of the default config, with a dict of config options.
        if isinstance(local_config, dict):
            for key in local_config:
                linter.global_set_option(key, local_config[key])

    linter.load_config_file()
    return linter


def _verify_pre_check(filepath):
    """Check student code for certain issues."""

    # Make sure the program doesn't crash for students.
    # Could use some improvement for better logging and error reporting.
    try:
        # Check for inline "pylint:" comment, which may indicate a student
        # trying to disable a check.
        with tokenize.open(filepath) as f:
            for (tok_type, content, _, _, _) in tokenize.generate_tokens(f.readline):
                if tok_type != tokenize.COMMENT:
                    continue
                match = pylint.utils.OPTION_RGX.search(content)
                if match is not None:
                    print('ERROR: string "pylint:" found in comment. ' +
                          'No check run on file `{}`\n'.format(filepath))
                    return False
    except IndentationError as e:
        print('ERROR: python_ta could not check your code due to an ' +
              'indentation error at line {}'.format(e.lineno))
        return False
    except tokenize.TokenError as e:
        print('ERROR: python_ta could not check your code due to a ' +
              'syntax error in your file')
        return False
    return True


def get_file_paths(rel_path):
    """A generator for iterating python files within a directory.
    `rel_path` is a relative path to a file or directory.
    Returns paths to all files in a directory.
    TODO: refactor helpers into a new file, `python_ta/utils.py`
    """
    if not os.path.isdir(rel_path):
        yield rel_path  # Don't do anything; return the file name.

    for root, _, files in os.walk(rel_path):
        for filename in (f for f in files if f.endswith('.py')):
            yield os.path.join(root, filename)  # Format path, from root.


def _check(module_name='', reporter=ColorReporter, number_of_messages=5, level='all',
           local_config='', pep8=False):
    """Check a module for problems, printing a report.

    The `module_name` can take several inputs:
    - a string of the directory, or file to check (`.py` extension is optional). 
    - a list of strings of directories or files.
    - or not provided, to check the current python file.

    `level` is used to specify which checks should be made.

    `local_config` is a dict of config options, or string of a config file name.
    """
    valid_module_names = []

    # Allow call to check with empty args
    if module_name == '':
        m = sys.modules['__main__']
        spec = importlib.util.spec_from_file_location(m.__name__, m.__file__)
        module_name = [spec.origin]
    # Enforce API to expect 1 file or directory if type is list
    elif isinstance(module_name, str):
        module_name = [module_name]
    # otherwise, enforce API to expect `module_name` type as list
    elif not isinstance(module_name, list):
        print('No checks run. Input to check, `{}`, has invalid type, must be a list of strings.\n'.format(module_name))
        return

    current_reporter = reporter(number_of_messages)
    linter = _load_pylint_plugins(current_reporter, local_config, pep8)
    
    patch_all()  # Monkeypatch pylint

    # Filter valid files to check.
    for item in module_name:
        if not isinstance(item, str):  # Issue errors for invalid types
            current_reporter.show_file_linted(item)
            print('No check run on file `{}`, with invalid type. Must be type: str.\n'.format(item))
        elif os.path.isdir(item):
            valid_module_names.append(item)
        elif not os.path.exists(item):
            # For files with dot notation, e.g., `examples.<filename>`
            try:
                filepath = modutils.file_from_modpath(item.split('.'))
                if os.path.exists(filepath):
                    valid_module_names.append(filepath)
                else:
                    current_reporter.show_file_linted(item)
                    print('Could not find the file called, `{}`\n'.format(item))
            except ImportError:
                current_reporter.show_file_linted(item)
                print('Could not find the file called, `{}`\n'.format(item))
        else:
            valid_module_names.append(item)  # Check other valid files.

    # Try to check file, issue error message for invalid files.
    try:
        for locations in valid_module_names:
            for file_py in get_file_paths(locations):
                current_reporter.show_file_linted(file_py)
                if not _verify_pre_check(file_py):
                    continue  # Check the other files
                linter.check(file_py)  # Lint !
                current_reporter.print_messages(level)
                current_reporter.reset_messages()  # Clear lists for any next file.

    except Exception as e:
        print('Unexpected error encountered - please report this to david@cs.toronto.edu!')
        print('Error message: "{}"'.format(e))
        raise e


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)
