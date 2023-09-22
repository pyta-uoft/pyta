"""Checker for the style of the file"""
import pycodestyle
from pylint.checkers import BaseRawFileChecker


class PycodestyleChecker(BaseRawFileChecker):
    """A checker class to report PEP8 style errors in the file.

    Use options to specify the list of PEP8 errors to ignore"""

    name = "pep8_errors"
    msgs = {"E9989": ("Found pycodestyle (PEP8) style error at %s", "pep8-errors", "")}

    options = (
        (
            "pycodestyle-ignore",
            {
                "default": (),
                "type": "csv",
                "metavar": "<pycodestyle-ignore>",
                "help": "List of Pycodestyle errors to ignore",
            },
        ),
    )

    def process_module(self, node):
        style_guide = pycodestyle.StyleGuide(
            paths=[node.stream().name],
            reporter=JSONReport,
            ignore=self.linter.config.pycodestyle_ignore,
        )
        report = style_guide.check_files()

        for line_num, msg in report.get_file_results():
            self.add_message("pep8-errors", line=line_num, args=msg)


class JSONReport(pycodestyle.StandardReport):
    def get_file_results(self):
        self._deferred_print.sort()
        return [
            (line_number, f"line {line_number}, column {offset}: {text}")
            for line_number, offset, _, text, _ in self._deferred_print
        ]


def register(linter):
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(PycodestyleChecker(linter))
