# Use os.walk to walk through all the files in a directory from top to bottem.
# Everytime when os.walk walks a file, check if the file is a python file, if
# it is, then run a check_all on it.
# os.walk doesn't return anything
import os
from python_ta import *



multi_files = False
# keeps track of who called stat_calculator, to tell StatReporter how to print


def pyta_statistics(directory):
    """
    Recursively run python_ta.check_all() on the files in directory to the files
    in its subdirectories.

    @param str directory: The string of the path way of the directory.
    @rtype: None
    """
    global multi_files
    multi_files = True


    # walk directory, find every "file":
    # Does check_all take "file" by itself? Need altered filepath?
    # check_all(file, reporter=StatReporter)


def stats_calculator(error_msgs, style_msgs):
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
    stats = {}

    # aggregate stats
    # TODO: does this aggregate stats itself or call helpers?

    return stats


def frequent_complaints(comp_dict, top="all"):
    """
    Sort the errors in error_dict from the most frequent to least frequent in a
    list.
    Return top couple most frequently occurred errors.

    @type comp_dict: dict
    @type top: str | int
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
        return most_frequently[0:top]
    else:
        return most_frequently


