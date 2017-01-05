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
import pylint
from astroid import MANAGER

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

    The name of the module should be the name of a module,
    or the path to a Python file.
    """
    _check(module_name=module_name, reporter=reporter, number_of_messages=number_of_messages, level='error', local_config_file=config)


def check_all(module_name='', reporter=ColorReporter, number_of_messages=5,
              config=''):
    """Check a module for errors and style warnings, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """
    _check(module_name, reporter, number_of_messages, level='all',
           local_config_file=config)


def _check(module_name='', reporter=ColorReporter, number_of_messages=5, level='all',
           local_config_file='', pep8=False):
    """Check a module for problems, printing a report.

    <level> is used to specify which checks should be made.

    The name of the module should be the name of a module,
    or the path to a Python file.
    """
    if module_name == '':
        m = sys.modules['__main__']
        spec = importlib.util.spec_from_file_location(m.__name__, m.__file__)
    else:
        # Check if `module_name` is not the type str, raise error.
        if not isinstance(module_name, str):
            print("The Module '{}' has an invalid name. Module name must be "
                  "type str.".format(module_name))
            return
        module_name = module_name.replace(os.path.sep, '.')

        # Detect if the extension .py is added, and if it is, remove it.
        if module_name.endswith('.py'):
            module_name = module_name[:-3]

        spec = importlib.util.find_spec(module_name)

    if spec is None:
        print("The Module '{}' could not be found. ".format(module_name))
        return

    # Clear the astroid cache of this module (allows for on-the-fly changes
    # to be detected in consecutive runs in the interpreter).
    if spec.name in MANAGER.astroid_cache:
        del MANAGER.astroid_cache[spec.name]

    current_reporter = reporter(number_of_messages)
    linter = lint.PyLinter(reporter=current_reporter)
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

    # Monkeypatch pylint
    patch_all()

    # Make sure the program doesn't crash for students.
    # Could use some improvement for better logging and error reporting.
    try:
        # Check for inline "pylint:" comment, which may indicate a student
        # trying to disable a check.
        # TODO: Put this into a helper function.
        with tokenize.open(spec.origin) as f:
            for (tok_type, content, _, _, _) in tokenize.generate_tokens(f.readline):
                if tok_type != tokenize.COMMENT:
                    continue
                match = pylint.utils.OPTION_RGX.search(content)
                if match is None:
                    continue
                else:
                    print('ERROR: string "pylint:" found in comment. No checks will be run.')
                    return
    except IndentationError as e:
        print('ERROR: python_ta could not check your code due to an ' +
              'indentation error at line {}'.format(e.lineno))
        return
    except tokenize.TokenError as e:
        print('ERROR: python_ta could not check your code due to a ' +
              'syntax error in your file')
        return

    try:
        linter.check([spec.origin])
        current_reporter.print_messages(level)

    except Exception as e:
        print('Unexpected error encountered - please report this to david@cs.toronto.edu!')
        print(e)


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)

