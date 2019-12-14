from pylint.interfaces import IRawChecker
import pycodestyle
from pylint.checkers import BaseChecker

# Ignored PEP8 checks (duplicated with pylint)
IGNORED_CHECKS = [
    'E501'
]


class PycodestyleChecker(BaseChecker):
    __implements__ = IRawChecker

    name = 'pep8_errors'
    msgs = {'E9989': ('Found PEP8 style error at %s', 'pep8-errors', '')}

    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    def process_module(self, node):
        style_guide = pycodestyle.StyleGuide(paths=[node.stream().name], reporter=JSONReport, ignore=IGNORED_CHECKS)
        report = style_guide.check_files()

        for line_num, msg in report.get_file_results():
            self.add_message('pep8-errors', line=line_num, args=msg)


class JSONReport(pycodestyle.StandardReport):
    def get_file_results(self):
        self._deferred_print.sort()
        return [
            (line_number, f'line {line_number}, column {offset}: {text}')
            for line_number, offset, _, text, _ in self._deferred_print
        ]


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(PycodestyleChecker(linter))
