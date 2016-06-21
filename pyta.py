"""Python Teaching Assistant

The goal of this module is to provide automated feedback to students in our
introductory Python courses, using static analysis of their code.

To run the checker, call the check function on the name of the module to check.

> import pyta
> pyta.check('mymodule')
"""
import importlib.util
import pylint.lint as lint
from reporters.color_reporter import ColorReporter

import webbrowser
import os
from urllib.request import pathname2url


# Local version of website; will be updated later.
HELP_URL = 'file:' + pathname2url(os.path.abspath('website/index.html'))


def check(module_name, reporter=ColorReporter):
    """Check a module for errors, printing a report.

    The name of the module should be passed in as a string,
    without a file extension (.py).
    """
    spec = importlib.util.find_spec(module_name)

    current_reporter = reporter()
    linter = lint.PyLinter(reporter=current_reporter)
    linter.load_default_plugins()
    linter.load_plugin_modules(['checkers/forbidden_import_checker',
                                'checkers/global_variables_checker',
                                'checkers/dynamic_execution_checker',
                                'checkers/IO_Function_checker'])
    linter.read_config_file()
    linter.load_config_file()
    linter.check([spec.origin])
    current_reporter.print_message_ids()


def doc(msg_id):
    """Open a webpage explaining the error for the given message."""
    msg_url = HELP_URL + '#' + msg_id
    print('Opening {} in a browser.'.format(msg_url))
    webbrowser.open(msg_url)



