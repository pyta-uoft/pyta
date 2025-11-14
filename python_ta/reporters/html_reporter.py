import os
import socket
import sys

from jinja2 import Environment, FileSystemLoader
from markdown_it import MarkdownIt
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import PythonLexer
from pylint.lint import PyLinter
from pylint.reporters.ureports.nodes import BaseLayout

from ..util.servers.one_shot_server import open_html_in_browser
from ..util.servers.persistent_server import PersistentHTMLServer
from .core import PythonTaReporter

TEMPLATES_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "templates")


class HTMLReporter(PythonTaReporter):
    """Reporter that displays results in HTML form.

    By default, automatically opens the report in a web browser.
    """

    name = "pyta-html"

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
    port = None
    persistent_server = None

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
        md = MarkdownIt()
        grouped_messages = {
            path: self.group_messages(msgs) for path, msgs in self.gather_messages().items()
        }

        template_f = self.linter.config.pyta_template_file
        template_f = (
            template_f if template_f != "" else os.path.join(TEMPLATES_DIR, "template.html.jinja")
        )
        path = os.path.abspath(template_f)
        filename, file_parent_directory = os.path.basename(path), os.path.dirname(path)

        template = Environment(loader=FileSystemLoader(file_parent_directory)).get_template(
            filename
        )
        if not self.port:
            self.port = (
                _find_free_port()
                if self.linter.config.server_port == 0
                else self.linter.config.server_port
            )
        if not self.persistent_server:
            self.persistent_server = PersistentHTMLServer(self.port)

        # Embed resources so the output html can go anywhere, independent of assets.
        # with open(os.path.join(TEMPLATES_DIR, 'pyta_logo_markdown.png'), 'rb+') as image_file:
        #     # Encode img binary to base64 (+33% size), decode to remove the "b'"
        #     pyta_logo_base64_encoded = b64encode(image_file.read()).decode()

        # Render the jinja template
        rendered_template = template.render(
            date_time=self._generate_report_date_time(),
            port=self.port,
            reporter=self,
            grouped_messages=grouped_messages,
            os=os,
            enumerate=enumerate,
            md=md,
        )

        # If a filepath was specified, write to the file
        if self.out is not sys.stdout:
            self.writeln(rendered_template)
            self.out.flush()
        else:
            rendered_template = rendered_template.encode("utf8")
            if self.linter.config.watch:
                self.persistent_server.start_server_once(rendered_template)
            else:
                open_html_in_browser(rendered_template, self.port)
                print(
                    "[INFO] Your PythonTA report is being opened in your web browser.\n"
                    "       If it doesn't open, please add an output argument to python_ta.check_all\n"
                    "       as follows:\n\n"
                    "         check_all(..., output='pyta_report.html')\n\n"
                    "       This will cause PythonTA to save the report to a file, pyta_report.html,\n"
                    "       that you can open manually in a web browser.",
                    file=sys.stderr,
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


def _find_free_port() -> int:
    """Find and return an available TCP port on localhost."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def register(linter: PyLinter):
    linter.register_reporter(HTMLReporter)
