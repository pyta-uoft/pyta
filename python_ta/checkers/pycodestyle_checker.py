from pylint.interfaces import IRawChecker
import pycodestyle
import io
from contextlib import redirect_stdout
from pylint.checkers import BaseChecker


class PycodestyleChecker(BaseChecker):
    __implements__ = IRawChecker

    name = 'pep8_errors'
    msgs = {'E9989': ('Found errors (and warnings)'
                      '%s', 'pep8-errors', '')}

    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    def process_module(self, node):
        style_checker = pycodestyle.Checker(node.stream().name)

        with io.StringIO() as buf, redirect_stdout(buf):
            num_errors = style_checker.check_all()
            output = buf.getvalue()
        output = output.replace('\n', '')
        output = output.split(':')
        self.add_message('pep8-errors', line=output[1],
                            args=output[3])

def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(PycodestyleChecker(linter))
