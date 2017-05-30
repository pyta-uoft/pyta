from .color_reporter import ColorReporter
from .html_reporter import HTMLReporter
from .plain_reporter import PlainReporter
from .stat_reporter import StatReporter

# Export tuple of reporter classes for python_ta init file.
REPORTERS = (ColorReporter, PlainReporter, HTMLReporter, StatReporter)
