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

from .reporters import ColorReporter
from .patches import patch_all

# Local version of website; will be updated later.
HELP_URL = 'http://www.cs.toronto.edu/~david/pyta/'


# check the python version
if sys.version_info < (3, 4, 0):
    print('You need Python 3.4 or later to run this script')


def check_errors(files_or_directory='', reporter=ColorReporter, 
                 number_of_messages=5, config=''):
    """Check a module for errors, printing a report.

    The name of the module should be the name of a module,
    or the path to a Python file.
    """
    _check(files_or_directory, reporter, number_of_messages, level='error', 
           local_config_file=config)


def check_all(files_or_directory='', reporter=ColorReporter, 
              number_of_messages=5, config=''):
    """Check a module for errors and style warnings, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """

    _check(files_or_directory, reporter, number_of_messages, level='all', 
           local_config_file=config)


def _load_pylint_plugins(current_reporter, local_config_file, pep8):
    """Register checker plugins for pylint. Return linter.
    """
    linter = lint.PyLinter(reporter=current_reporter)
    # Register standard pylint checkers.
    linter.load_default_plugins()
    linter.load_plugin_modules(['python_ta/checkers/forbidden_import_checker',
                                'python_ta/checkers/global_variables_checker',
                                'python_ta/checkers/dynamic_execution_checker',
                                'python_ta/checkers/IO_Function_checker',
                                # TODO: Fix this test
                                #'python_ta/checkers/invalid_range_index_checker',
                                'python_ta/checkers/assigning_to_self_checker',
                                'python_ta/checkers/always_returning_checker'])
    if pep8:
        linter.load_plugin_modules(['python_ta/checkers/pycodestyle_checker'])
    if local_config_file != '':
        linter.read_config_file(local_config_file)
    else:
        linter.read_config_file(os.path.join(os.path.dirname(__file__), '.pylintrc'))
    linter.load_config_file()
    return linter


def _find_inline_pylint_comment(spec):
    """Check student code for certain issues."""

    # Make sure the program doesn't crash for students.
    # Could use some improvement for better logging and error reporting.
    try:
        # Check for inline "pylint:" comment, which may indicate a student
        # trying to disable a check.
        with tokenize.open(spec) as f:
            for (tok_type, content, _, _, _) in tokenize.generate_tokens(f.readline):
                if tok_type != tokenize.COMMENT:
                    continue
                match = pylint.utils.OPTION_RGX.search(content)
                if match is None:
                    continue
                else:
                    print('ERROR: string "pylint:" found in comment. ' +
                          'No checks will be run.')
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


def _check(files_or_directory='', reporter=ColorReporter, number_of_messages=5, 
           level='all', local_config_file='', pep8=False):
    """Check a module for problems, printing a report.

    <level> is used to specify which checks should be made.

    The name of the module should be the name of a module,
    or the path to a Python file.
    """

    # Check if `module_name` is not the type str, raise error.
    if not isinstance(files_or_directory, str):
        print('No checks run. Input to check, `{}`, has invalid type, must be type: str.'.format(files_or_directory))
        return

    current_reporter = reporter(number_of_messages)
    linter = _load_pylint_plugins(current_reporter, local_config_file, pep8)
    patch_all()  # Monkeypatch pylint
    try:
        files_or_directory_l = list(filter(None, files_or_directory.split(' ')))
        linter.open()  # initialize stats

        expanded_files, errors = utils.expand_modules(files_or_directory_l, 
                        linter.config.black_list, linter.config.black_list_re)
        for error in errors:
            current_reporter.show_file_linted(error['mod'])
            if isinstance(error['ex'], ImportError):
                print('Error: {}, which means the file "{}" could not be found.\n'
                      .format(error['ex'], error['mod']))
            else:
                print('Error: {}\n'.format(error['ex']))
        print()

        for descr in expanded_files:
            modname, filepath, is_arg = descr['name'], descr['path'], descr['isarg']
            if not _find_inline_pylint_comment(filepath):
                return
            current_reporter.show_file_linted(modname)
            linter.check(filepath)  # Lint !
            current_reporter.print_messages(level)

    except Exception as e:
        print('Unexpected error encountered - please report this to ' +
              'david@cs.toronto.edu!')
        print(e)
        raise e


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)
