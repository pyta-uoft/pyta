from .color_reporter import ColorReporter
from .html_reporter import HTMLReporter
from .json_reporter import JSONReporter
from .lsp_reporter import LSPReporter
from .plain_reporter import PlainReporter

# Export tuple of reporter classes for python_ta init file.
REPORTERS = (ColorReporter, PlainReporter, HTMLReporter, JSONReporter, LSPReporter)
