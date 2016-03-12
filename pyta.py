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

def check(module_name):
    spec = importlib.util.find_spec(module_name)

    reporter = PyTAReporter()
    linter = lint.PyLinter(reporter=reporter)
    linter.load_default_plugins()
    linter.check([spec.origin])
    reporter.print_message_ids()


class PyTAReporter(BaseReporter):
    def __init__(self):
        super().__init__(self)
        self._messages = []

    def handle_message(self, msg):
        """Handle a new message triggered on the current file."""
        self._messages.append(msg)

    def print_message_ids(self):
        for msg in self._messages:
            print(msg.msg_id)
