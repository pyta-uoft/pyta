import os
import sys
import webbrowser
from base64 import b64encode
from datetime import datetime
from http.server import BaseHTTPRequestHandler, HTTPServer

from jinja2 import Environment, FileSystemLoader
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import PythonLexer
from pylint.interfaces import IReporter
from pylint.reporters.ureports.nodes import BaseLayout

from .core import PythonTaReporter

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
        template = Environment(loader=FileSystemLoader(TEMPLATES_DIR)).get_template(template_f)

        # Embed resources so the output html can go anywhere, independent of assets.
        # with open(os.path.join(TEMPLATES_DIR, 'pyta_logo_markdown.png'), 'rb+') as image_file:
        #     # Encode img binary to base64 (+33% size), decode to remove the "b'"
        #     pyta_logo_base64_encoded = b64encode(image_file.read()).decode()

        # Date/time (24 hour time) format:
        # Generated: ShortDay. ShortMonth. PaddedDay LongYear, Hour:Min:Sec
        dt = str(datetime.now().strftime("%a. %b. %d %Y, %I:%M:%S %p"))

        # Render the jinja template
        rendered_template = template.render(
            date_time=dt,
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
            self._open_html_in_browser(rendered_template)

    def _open_html_in_browser(self, html: bytes) -> None:
        """
        Display html in a web browser without creating a temp file.
        Instantiates a trivial http server and uses the webbrowser module to
        open a URL to retrieve html from that server.

        Adapted from: https://github.com/plotly/plotly.py/blob/master/packages/python/plotly/plotly/io/_base_renderers.py#L655
        """

        class OneShotRequestHandler(BaseHTTPRequestHandler):
            def do_GET(self):
                self.send_response(200)
                self.send_header("Content-type", "text/html")
                self.end_headers()

                buffer_size = 1024 * 1024
                for i in range(0, len(html), buffer_size):
                    self.wfile.write(html[i : i + buffer_size])

            def log_message(self, format, *args):
                """Overridden so that no server logging is printed."""
                pass

        server = HTTPServer(("127.0.0.1", 0), OneShotRequestHandler)
        webbrowser.open(f"http://127.0.0.1:{server.server_port}", new=2)
        server.handle_request()
        server.server_close()
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
