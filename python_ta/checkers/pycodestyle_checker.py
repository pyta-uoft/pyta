from typing import List, Tuple

import pycodestyle
from astroid import nodes
from pylint.checkers import BaseRawFileChecker
from pylint.lint import PyLinter


class PycodestyleChecker(BaseRawFileChecker):
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

    # this is important so that your checker is executed before others
    priority = -1

    def process_module(self, node: nodes.NodeNG) -> None:
        style_guide = pycodestyle.StyleGuide(
            paths=[node.stream().name],
            reporter=JSONReport,
            ignore=self.linter.config.pycodestyle_ignore,
        )
        report = style_guide.check_files()

        for line_num, msg in report.get_file_results():
            self.add_message("pep8-errors", line=line_num, args=msg)


class JSONReport(pycodestyle.StandardReport):
    def get_file_results(self) -> List[Tuple]:
        self._deferred_print.sort()
        return [
            (line_number, f"line {line_number}, column {offset}: {text}")
            for line_number, offset, _, text, _ in self._deferred_print
        ]


def register(linter: PyLinter) -> None:
    """required method to auto register this checker"""
    linter.register_checker(PycodestyleChecker(linter))
