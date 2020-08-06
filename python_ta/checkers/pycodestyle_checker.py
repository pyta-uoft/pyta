from pylint.interfaces import IRawChecker
import pycodestyle
from pylint.checkers import BaseChecker

# Ignored pycodestyle checks (mostly duplicated with pylint)
IGNORED_CHECKS = [
    'E111',  # pylint W0311
    'E114',  # pylint W0311
    'E117',  # pylint W0311
    'E401',  # pylint C0410
    'E402',  # pylint C0413
    'E501',  # pylint C0301
    'E701',  # pylint C0321
    'E702',  # pylint C0321
    'E703',  # pylint W0301
    'E711',  # pylint C0121
    'E712',  # pylint C0121
    'E722',  # pylint W0702
    'W291',  # pylint C0303
    'W292',  # pylint C0304
    'W293',  # pylint C0303
    'W391',  # pylint C0305
    'W503'   # this one just conflicts with pycodestyle W504
]


class PycodestyleChecker(BaseChecker):
    __implements__ = IRawChecker

    name = 'pep8_errors'
    msgs = {'E9989': ('Found pycodestyle (PEP8) style error at %s', 'pep8-errors', '')}

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
