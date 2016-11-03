from pylint.interfaces import IRawChecker
import pycodestyle
import io
from contextlib import redirect_stdout
from pylint.checkers import BaseChecker


class PycodestyleChecker(BaseChecker):
    __implements__ = IRawChecker

    name = 'pep8_errors'
    msgs = {'E9989': ('Found pep8 errors (and warnings)'
                      '%s', 'pep8-errors', '')}

    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    def process_module(self, node):
        style_checker = pycodestyle.Checker(node.stream().name)

        # catch the output of check_all() in pycodestyle
        with io.StringIO() as buf, redirect_stdout(buf):
            style_checker.check_all()
            output = buf.getvalue()

        # Handle the case of multiple error messages
        lst = output.split('\n')

        for line in lst:
            if line != '':
                line = line.split(':')
                self.add_message('pep8-errors', line=line[1],
                                 args=line[3])


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(PycodestyleChecker(linter))
