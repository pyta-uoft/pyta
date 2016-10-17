import os
import python_ta
from python_ta.reporters.stat_reporter import StatReporter
from sample_usage.stats_analysis import summary
from collections import OrderedDict


def pyta_statistics(directory):
    """
    Recursively run python_ta.check_all() on the files in the directory and its
    subdirectories to collect the error and style messages.
    Assume directory is a folder that contains subdirectories named by
    student's UTORid/studentID/group name, or directory can also be a student
    folder itself. Also assume that student's directory doesn't contain any
    subdirectories, only files.

    @param str directory: The string of the path way of the directory.
    @rtype: None
    """
    all_errors = OrderedDict()
    for root_str, dir_list, file_list in os.walk(directory):
        # check if directory is student directory or assignment parent directory
        if dir_list == []:
            # It is a student folder
            student_id = os.path.basename(root_str)
            student_errors = []
            student_style = []
            for file in file_list:
                # check if file is a .py file
                if file.endswith(".py"):
                    python_ta.check_all(os.path.join(student_id, file),
                                        reporter=StatReporter)
                    # store all the msg objects of this student's files
            student_errors.extend(StatReporter.error_messages)
            student_style.extend(StatReporter.style_messages)
            all_errors[student_id] = (student_errors, student_style)
            StatReporter.reset_messages()

    if len(all_errors) < 1:
        raise Exception("No student files found in given directory!")

    _print_stats(*summary(all_errors))


def _print_stats(individual_stats, summary_stats):
    """
    Pretty prints the statistics aggregated by summary.

    Format:
    ===================== Statistics per Student/Group =====================
    Student/group: <student/group id>
        Most Frequent Messages:
            1. <Error Type 1>: <number> (<percentage>%)
            2. ...
        Most Frequent Errors:
            1. ...
        Most Frequent Styles:
            1. ...

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    Student/group: ...
        ...

    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


    ================== Aggregate Statistics for Directory ==================
    Top 5 Frequent Code Errors:
        1. <Error Type 1>: <number> (<percentage>%)
        2. ...
    Average Code Errors Per Student: <number>

    Top 5 ...
        ...
    ...

    ...

    ======= Five Number Summary =======
        Most:                <number>
        Upper Quartile (Q3): <number>
        Median:              <number>
        Lower Quartile (Q1): <number>
        Least:               <number>

    ~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~


    @param OrderedDict[str, List] individual_stats:
        stats computed per student/group
    @param OrderedDict[str, List | OrderedDict] summary_stats:
        stats computed over all the students
    @rtype: dict
    """
    # TODO: make aggregate stats conform to format
    if summary_stats:
        print("=====================", "Statistics per Student/Group",
              "=====================")
    for student_name, stats in individual_stats.items():
        print("Student/group:", student_name)
        for stat_type, results in stats:
            print("\t" + stat_type + ":")
            _print_top_errors(results)
        print("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n")

    if summary_stats:
        print("\n==================",
              "Aggregate Statistics for Directory", "==================")
        # Top 5 Frequent Code Errors
        stat_type, stats = summary_stats[0]
        print(stat_type + ":")
        _print_top_errors(stats, tabs=1)

        # Average Code Errors Per Student
        print("{}: {}\n".format(summary_stats[1][0], summary_stats[1][1]))

        # Top 5 Frequent Style Errors
        stat_type, stats = summary_stats[2]
        print(stat_type + ":")
        _print_top_errors(stats, tabs=1)

        # Average Style Errors Per Student
        print("{}: {}\n".format(summary_stats[3][0], summary_stats[3][1]))

        # Five Number Summary
        print("=======", summary_stats[4][0], "=======")
        five_numbers = summary_stats[4][1]
        for stat_type, value in five_numbers:
            print("\t{}:{}{}".format(stat_type, ' ' * (20 - len(stat_type)),
                                     value))

        print("\n~" + "=~" * 37)


def _print_top_errors(stats, tabs=2):
    """
    Pretty prints a list of most frequent errors and their counts.

    @param list[tuple(str, int)] stats: the errors and counts to be printed
    @rtype: None
    """
    i = 1
    while i <= len(stats):
        print("{}{}. {}: {}".format("\t" * tabs, i, stats[i][0], stats[i][1]))
