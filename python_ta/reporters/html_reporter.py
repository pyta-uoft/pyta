import os
import sys

from jinja2 import Environment, FileSystemLoader
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import PythonLexer
from pylint.reporters.ureports.nodes import BaseLayout

from .core import PythonTaReporter
from .html_server import open_html_in_browser

TEMPLATES_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "templates")


class HTMLReporter(PythonTaReporter):
    """Reporter that displays results in HTML form.

    By default, automatically opens the report in a web browser.
    """

    name = "HTMLReporter"

    _COLOURING = {
        "black": '<span class="black">',
        "black-line": '<span class="black line-num">',
        "bold": "<span>",
        "code-heading": "<span>",
        "style-heading": "<span>",
        "code-name": "<span>",
        "style-name": "<span>",
        "highlight": '<span class="highlight-pyta">',
        "grey": '<span class="grey">',
        "grey-line": '<span class="grey line-num">',
        "gbold": '<span class="gbold">',
        "gbold-line": '<span class="gbold line-num">',
        "reset": "</span>",
    }
    _PRE_LINE_NUM_SPACES = 0

    no_err_message = "No problems detected, good job!"
    no_snippet = "No code to display for this message."
    code_err_title = "Code Errors or Forbidden Usage (fix: high priority)"
    style_err_title = "Style or Convention Errors (fix: before submission)"
    OUTPUT_FILENAME = "pyta_report.html"

    def print_messages(self, level="all"):
        """Do nothing to print messages, since all are displayed in a single HTML file."""

    def display_messages(self, layout: BaseLayout) -> None:
        """Hook for displaying the messages of the reporter

        This will be called whenever the underlying messages
        needs to be displayed. For some reporters, it probably
        doesn't make sense to display messages as soon as they
        are available, so some mechanism of storing them could be used.
        This method can be implemented to display them after they've
        been aggregated.
        """
        grouped_messages = {path: self.group_messages(msgs) for path, msgs in self.messages.items()}

        template_f = self.linter.config.pyta_template_file
        template_f = (
            template_f if template_f != "" else os.path.join(TEMPLATES_DIR, "template.html.jinja")
        )
        path = os.path.abspath(template_f)
        filename, file_parent_directory = os.path.basename(path), os.path.dirname(path)

        template = Environment(loader=FileSystemLoader(file_parent_directory)).get_template(
            filename
        )

        # Embed resources so the output html can go anywhere, independent of assets.
        # with open(os.path.join(TEMPLATES_DIR, 'pyta_logo_markdown.png'), 'rb+') as image_file:
        #     # Encode img binary to base64 (+33% size), decode to remove the "b'"
        #     pyta_logo_base64_encoded = b64encode(image_file.read()).decode()

        # Render the jinja template
        rendered_template = template.render(
            date_time=self._generate_report_date_time(),
            reporter=self,
            grouped_messages=grouped_messages,
            os=os,
            enumerate=enumerate,
        )

        # If a filepath was specified, write to the file
        if self.out is not sys.stdout:
            self.writeln(rendered_template)
        else:
            rendered_template = rendered_template.encode("utf8")
            open_html_in_browser(
                rendered_template, self.linter.config.watch, self.linter.config.server_port
            )

    @classmethod
    def _colourify(cls, colour_class: str, text: str) -> str:
        """Return a colourized version of text, using colour_class."""
        colour = cls._COLOURING[colour_class]
        new_text = text.replace(" ", cls._SPACE)
        if "-line" not in colour_class:
            new_text = highlight(
                new_text,
                PythonLexer(),
                HtmlFormatter(nowrap=True, lineseparator="", classprefix="pygments-"),
            )

        return colour + new_text + cls._COLOURING["reset"]
