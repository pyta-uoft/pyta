"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import pyta
> pyta.check('mymodule')
"""
import importlib.util
import pylint.lint as lint
from pylint.reporters import BaseReporter
from astroid import MANAGER

import webbrowser
import sys


# Local version of website; will be updated later.
HELP_URL = 'http://www.cs.toronto.edu/~david/pyta/'

# check the python version
if sys.version_info < (3, 4, 0):
    print('You need Python 3.4 or later to run this script')


def check(module_name):
    """Check a module for errors, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """
    # Check if `module_name` is not the type str, raise error.
    if not isinstance(module_name, str):
        print("The Module '{}' has an invalid name. Module name must be the "
              "type str.".format(module_name))
        return

    # Detect if the extension .py is added, and if it is, remove it.
    if module_name.endswith('.py'):
        module_name = module_name[:-3]

    # Reset astroid cache
    MANAGER.astroid_cache.clear()

    spec = importlib.util.find_spec(module_name)

    reporter = PyTAReporter()
    linter = lint.PyLinter(reporter=reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['checkers/forbidden_import_checker',
                                'checkers/global_variables_checker',
                                'checkers/dynamic_execution_checker',
                                'checkers/IO_Function_checker',
                                'checkers/always_returning_checker'])
    linter.read_config_file()
    linter.load_config_file()

    # When module is not found, raise exception.
    try:
        linter.check([spec.origin])
    except AttributeError:
        print("The Module '{}' could not be found. ".format(module_name))
        return
            
    reporter.print_message_ids()

def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)


class PyTAReporter(BaseReporter):
    def __init__(self):
        super().__init__(self)
        self._messages = []

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        self._messages.append(msg)

    def print_message_ids(self):
        # Sort the messages by their type.
        self._messages.sort(key=lambda s: s[0])

        for msg in self._messages:
            if msg.msg_id.startswith('E'):
                # Error codes appear in red
                code = '\033[1;31m' + msg.msg_id + '\033[0m:'
            else:
                code = '\033[1m' + msg.msg_id + '\033[0m:'

            print(code, '({})\n    {}'.format(msg.symbol, msg.msg))
