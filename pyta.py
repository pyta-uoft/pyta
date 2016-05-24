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

import webbrowser
import os
from urllib.request import pathname2url

# Local version of website; will be updated later.
HELP_URL = 'file:' + pathname2url(os.path.abspath('website/index.html'))


def check(module_name):
    """Check a module for errors, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """
    spec = importlib.util.find_spec(module_name)
    reporter = PyTAReporter()
    linter = lint.PyLinter(reporter=reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['checkers/dynamic_execution_checker'])
    linter.load_plugin_modules(['checkers/forbidden_import_checker'])
    linter.read_config_file()
    linter.load_config_file()
    linter.check([spec.origin])
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
