from .plain_reporter import PlainReporter


class StatReporter(PlainReporter):
    error_messages = []
    style_messages = []

    def __init__(self, source_lines=None):
        """Initialize a StatReporter.

        Clear the two class-level message lists.

        @type source_lines: List[str]
        @rtype: None
        """
        super().__init__(source_lines)
        StatReporter.error_messages = []
        StatReporter.style_messages = []

    def print_messages(self, level="all"):
        """Override the corresponding function in PlainReporter.

        @type level: str
        @rtype: None
        """
        StatReporter.error_messages.extend(self._error_messages)
        StatReporter.style_messages.extend(self._style_messages)

    # to appease PyCharm's NotImplemented complaint
    _display = None
