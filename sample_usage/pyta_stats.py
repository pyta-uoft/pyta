import os
import python_ta
from python_ta.reporters.stat_reporter import StatReporter
from sample_usage.stats_analysis import summary


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
    all_errors = {}
    for root_str, dir_list, file_list in os.walk(directory):
        # check if directory is student directory or assignment parent directory
        if not dir_list:
            # It is a student folder
            student_errors = []
            student_style = []
            for file in file_list:
                # check if file is a .py file
                if file[-3:] == ".py":
                    python_ta.check_all(os.path.join(root_str, file),
                                        reporter=StatReporter)
                    # store all the msg objects of this student's files
                    student_errors.extend(StatReporter.error_messages)
                    student_style.extend(StatReporter.style_messages)
                    student_id = os.path.basename(root_str)
                    all_errors[student_id] = (student_errors, student_style)  # TODO: ordered students?

                    StatReporter.reset_messages()
    _print_stats(*summary(all_errors))


def _print_stats(individual_stats, summary_stats):
    """
    Pretty prints the statistics aggregated by summary.

    @param list individual_stats: stats computed per student/group
    @param list summary_stats: stats computed over all the students
    @rtype: dict
    """
    if summary_stats:
        print("=========================", "Statistics per Student/Group",
              "=========================")
    for student_name, (error_dict, style_dict) in individual_stats:  # TODO
        print("Student/group:", student_name)
        print("\t=== Code errors ===")
        for stat_type, stats in error_dict.items():
            print("\t" + stat_type + ":")
            _print_top_errors(stats)

        print("\t=== Style errors ===")
        for stat_type, stats in style_dict.items():
            print("\t" + stat_type + ":")
            _print_top_errors(stats)
        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")

    if summary_stats:
        print("\n\n======================",
              "Aggregate Statistics for Directory", "======================")
        # Top 5 Frequent Code Errors
        stat_type, stats = summary_stats[0]
        print(stat_type + ":")
        _print_top_errors(stats, tabs=1)

        # Average Code Errors Per Student
        print("\n{}: {}".format(summary_stats[1][0], summary_stats[1][1]))

        # Top 5 Frequent Style Errors
        stat_type, stats = summary_stats[2]
        print(stat_type + ":")
        _print_top_errors(stats, tabs=1)

        # Average Style Errors Per Student
        print("\n{}: {}".format(summary_stats[3][0], summary_stats[3][1]))

        # Five Number Summary
        print("===", summary_stats[4][0], "===")
        five_numbers = summary_stats[4][1]
        for stat_type, value in five_numbers:
            print("\t{}: {}".format(stat_type, value))

        print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" * 2)


def _print_top_errors(stats, tabs=2):
    """
    Pretty prints a list of most frequent errors and their counts.

    @param list[tuple(str, int)] stats: the errors and counts to be printed
    @rtype: None
    """
    i = 1
    while i <= len(stats):
        print("{}{}. {}: {}".format("\t" * tabs, i, stats[i][0], stats[i][1]))
