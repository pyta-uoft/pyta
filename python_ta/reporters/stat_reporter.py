from .plain_reporter import PlainReporter


class StatReporter(PlainReporter):

    error_messages = []
    style_messages = []

    def __init__(self, number_of_messages):
        """
        Inherited from class PlainReporter.

        @type self: StatReporter
        @type number_of_messages: int
        @rtype: None
        """
        super().__init__(number_of_messages)

    def print_messages(self, level='all'):
        """
        Overrides the corresponding function in PlainReporter.


        @type self: StatReporter
        @type level: str
        @rtype: None
        """
        StatReporter.error_messages.extend(self._error_messages)
        StatReporter.style_messages.extend(self._style_messages)

    # to appease PyCharm's NotImplemented complaint
    _display = None


def reset_messages():
    """
    Resets the class-level lists that hold the message lists to empty, so as to
    avoid aggregating all files' messages in the StatReporter.
    Called by pyta_statistics before every instantiation of StatReporter by
    python_ta.check_all().

    @rtype: None
    """
    StatReporter.error_messages = []
    StatReporter.style_messages = []
