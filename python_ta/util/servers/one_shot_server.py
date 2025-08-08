import sys
import webbrowser
from http.server import BaseHTTPRequestHandler, HTTPServer


def open_html_in_browser(html: bytes, port: int) -> None:
    """
    Display html in a web browser without creating a temp file.
    Instantiates a trivial HTTP server on the specified port (or an available port if 0 is provided)
    and uses the webbrowser module to open a URL to retrieve the HTML from that server.

    Adapted from: https://github.com/plotly/plotly.py/blob/master/packages/python/plotly/plotly/io/_base_renderers.py#L655
    """

    class RequestHandler(BaseHTTPRequestHandler):
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

    server = HTTPServer(("127.0.0.1", port), RequestHandler)
    webbrowser.open(f"http://127.0.0.1:{server.server_port}", new=2)
    server.handle_request()
    server.server_close()
