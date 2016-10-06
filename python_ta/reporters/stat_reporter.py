from sample_usage import pyta_stats as stats
from .plain_reporter import PlainReporter


# Report the results from pyta_stats.py


class StatReporter(PlainReporter):

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
        # self.sort_messages()
        results = stats.stats_calculator(self._error_messages,
                                         self._style_messages)
        if stats.multi_files:
            # write results to file
            pass
        else:   # meaning check_all was called with StatReporter by user
            # print results to terminal/console
            pass

    # to appease PyCharm's NotImplemented complaint
    _display = None
