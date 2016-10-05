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
        # TODO
