import os
import python_ta
from python_ta.reporters.stat_reporter import StatReporter
from .stats_analysis import *


def pyta_statistics(directory):
    """
    Recursively run python_ta.check_all() on the files in the directory and its
    subdirectories to collect the error and style messages.
    Assume directory is a folder that contains subdirectories named by
    student's utorid/studentID/group name, or directory can also be a student
    folder itself. Also assume that student's directory doesn't contain any
    subdirectories, only files.

    @param str directory: The string of the path way of the directory.
    @rtype: None
    """
    all_errors = []
    all_style = []
    all_stats = {}
    for root_str, dir_list, file_list in os.walk(directory):
        # check if directory is student directory or assignment parent directory
        if dir_list is []:
            # It is a student folder
            for file in file_list:
                # check if file is a .py file
                if file[-3:] == ".py":
                    python_ta.check_all(file, reporter=StatReporter)
                    # store all the msg objects of this student's files
                    all_errors.extend(StatReporter.error_messages)
                    all_style.extend(StatReporter.style_messages)
                    student_id = os.path.basename(os.path.normpath(root_str))
                    all_stats[student_id] = stats_calculator(all_errors,
                                                             all_style)
                    StatReporter.reset_messages()
    return all_stats


def frequent_messages(comp_dict, top=5):
    """
    Sort the errors in error_dict from the most frequent to least frequent in a
    list.
    Return top couple most frequently occurred errors.

    @type comp_dict: dict
    @type top: int
    @rtype: list
    """
    # get key-value pair in a list
    most_frequently = list(comp_dict.items())
    # sort the list according to the value
    most_frequently.sort(key=lambda p: p[1])
    # from larger number to lower number
    most_frequently.reverse()
    # So the name of the error first and then the number of its occurrence.
    # return the top whatever number
    if isinstance(top, int) and top > 0:
        if top > len(most_frequently):
            top = len(most_frequently)
            return most_frequently[0:top]
        else:
            return most_frequently[0:top]
    else:
        raise TypeError("No!! Put a positive integer please.")
