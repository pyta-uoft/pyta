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
        if not dir_list:
            # It is a student folder
            student_id = os.path.basename(root_str)

            for file in file_list:
                # check if file is a .py file
                if file.endswith(".py"):
                    python_ta.check_all(os.path.join(student_id, file),
                                        reporter=StatReporter)
                    # store all the msg objects of this student's files
            all_errors[student_id] = (StatReporter.error_messages,
                                      StatReporter.style_messages)
            StatReporter.reset_messages()

    if len(all_errors) < 1:
        raise Exception("No student files found in given directory!")

    _print_stats(*summary(all_errors))


def _print_stats(individual_stats, summary_stats):
    """Pretty prints the statistics aggregated by summary.

    @param OrderedDict[str, List] individual_stats:
        stats computed per student/group
    @param OrderedDict[str, List | OrderedDict] summary_stats:
        stats computed over all the students
    @rtype: dict

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
        1. <Error Type 1>: <number>
        2. ...
    Average Code Errors Per Student: <number>

    Top 5 ...
        ...
    ...

    ...

    ======= Five Number Summary of Errors Per Student =======
        Most Errors:         <number>
        Upper Quartile (Q3): <number>
        Median:              <number>
        Lower Quartile (Q1): <number>
        Least Errors:        <number>

    ~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~=~
    """
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
        _print_top_errors(stats, tabs=1, per=False)

        # Average Code Errors Per Student
        print("{}: {}\n".format(summary_stats[1][0], summary_stats[1][1]))

        # Top 5 Frequent Style Errors
        stat_type, stats = summary_stats[2]
        print(stat_type + ":")
        _print_top_errors(stats, tabs=1, per=False)

        # Average Style Errors Per Student
        print("{}: {}\n".format(summary_stats[3][0], summary_stats[3][1]))

        # Top 5 Frequent Errors of Either Type
        stat_type, stats = summary_stats[4]
        print(stat_type + ":")
        _print_top_errors(stats, tabs=1, per=False)

        # Average Errors of Either Type Per Student
        print("{}: {}\n".format(summary_stats[5][0], summary_stats[5][1]))

        # Five Number Summary
        print("=======", summary_stats[6][0], "=======")
        five_numbers = summary_stats[6][1]
        for stat_type, value in five_numbers:
            print("\t{}:{}{}".format(stat_type, ' ' * (20 - len(stat_type)),
                                     value))

        print("\n~" + "=~" * 37)


def _print_top_errors(stats, tabs=2, per=True):
    """Pretty prints a list of most frequent errors and their counts.

    @param List[Tuple[str, int | Tuple]] stats: the errors & counts to print
    @param int tabs: the number of tabs to print before every line
    @param bool per: whether the stats are number-percentage tuples
    @rtype: None
    """
    for i, stat in enumerate(stats):
        print("{}{}. {}:".format("\t" * tabs, i + 1, stat[0]), end='')
        if per:
            print("{} ({}%)".format(stat[1][0], stat[1][1]))
        else:
            print(stat[1])
