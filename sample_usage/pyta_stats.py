import os
from os.path import join
import python_ta
from python_ta.reporters.stat_reporter import StatReporter

# keeps track of who called stat_calculator, to tell StatReporter how to print
multi_files = False
# make sure these two variables get set back to [] after
error_messages = []
style_messages = []


def pyta_statistics(directory):
    """
    Recursively run python_ta.check_all() on the files in the directory and its
    subdirectories to collect the error and style messages.

    @param str directory: The string of the path way of the directory.
    @rtype: None
    """
    global multi_files
    multi_files = True
    # store information to error_messages and style_messages
    global error_messages
    global style_messages
    for root_str, dir_list, file_list in os.walk(directory):
        for file in file_list:
            # check if file is a .py file
            if file[-3:] == ".py":
                python_ta.check_all(file, reporter=StatReporter)
                # store all the msg objects of this student's files
                error_messages.append(StatReporter._error_messages)
                style_messages.append(StatReporter._style_messages)


def stats_calculator(error_msgs, style_msgs): #these two things will be lists of Message objects
    """
    Analyse the given lists of error and style Message objects to aggregate
    statistics on and return them in dictionary form.
    Called by StatReporter.
    Results dictionary format:
    TODO
    @param list error_msgs: Message objects for all errors found by linters
    @param list style_msgs: Message objects for all style issues
    @rtype: dict
    """

    # {msg.symbol + "(" + msg.object + ")": count}
    all_msgs = error_msgs + style_msgs
    # get dict of values {id:int, id2:int}
    msgs_dict = calculator(all_msgs)
    # sort into list of tuple, highest on top
    freq_nums = frequent_complaints(msgs_dict)

    total_errors = sum([msgs_dict[msg_id] for msg_id in msgs_dict])
    # divide each value by total and round to two places
    for message in msgs_dict:
        msgs_dict[message] = (msgs_dict[message]/total_errors * 100).__round__(2)
    perc_nums = frequent_complaints(msgs_dict)
    stats = {'Most Frequent Messages In Numbers': freq_nums, 'Most Frequent Messages In Percentages': perc_nums}

    return stats

    # return dict = {"error" : int}


def calculator(msgs):
    """
    Returns the number of errors for msgs.
    :param list[Message] msgs: Message objects for all errors found by linters
    :rtype: dict
    """

    included = []
    msgs_dict = {}

    for msg in msgs:
        if msg.msg_id not in included:
            msgs_dict[msg.msg_id + "(" + msg.symbol + ")"] = msgs.count(msg.msg_id)
            included.append(msg.msg_id)
    return msgs_dict


def frequent_complaints(comp_dict, top=5):
    """
    Sort the errors in error_dict from the most frequent to least frequent in a
    list.
    Return top couple most frequently occurred errors.

    @type comp_dict: dict
    @type top: int
    @rtype: list
    """
    # get key-value pair in a list
    most_frequently = [pair for pair in comp_dict.items()]
    # sort the list according to the value
    most_frequently.sort(key=lambda p: p[1])
    # from larger number to lower number
    most_frequently.reverse()
    # So the name of the error first and then the number of its occurrence.
    # return the top whatever number
    if isinstance(top, int):
        if top < StatReporter._number_of_messages:
            top = StatReporter._number_of_messages
            return most_frequently[0:top]
        else:
            return most_frequently[0:top]
    else:
        raise TypeError("No!! Put a positive integer please.")
