import os
import python_ta
from python_ta.reporters.stat_reporter import StatReporter
from sample_usage.stats_analysis import summary
from collections import OrderedDict


def pyta_statistics(directory, config=''):
    """
    Recursively run python_ta.check_all() on the files in the directory and its
    subdirectories to collect the error and style messages.
    Assume directory is a folder that contains subdirectories named by
    student's UTORid/studentID/group name, or directory can also be a student
    folder itself. Also assume that student's directory doesn't contain any
    subdirectories, only files.

    @param str directory: The string of the path way of the directory.
    @param str config: A path to the configuration file to use.
    @rtype: dict[str, str]
    """
    all_errors = OrderedDict()

    for root_str, dir_list, file_list in os.walk(directory):
        # check if directory is student directory
        if len(dir_list) == 0:
            student_id = os.path.basename(root_str)

            for file in file_list:
                if file.endswith('.py'):
                    python_ta.check_all(os.path.join(root_str, file),
                                        reporter=StatReporter,
                                        config=config,
                                        number_of_messages=0)
                    # store all the msg objects of this student's files
            all_errors[student_id] = (StatReporter.error_messages,
                                      StatReporter.style_messages)

    if len(all_errors) == 0:
        raise Exception('No student files found in given directory!')
    else:
        _print_stats(*summary(all_errors))
        return all_errors


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
        Totals:
            Error and Style Messages: <number>
            Error Messages:           <number>
            Style Messages:           <number>

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
    Most Frequent Code Errors:
        1. <Error Type 1>: <number>
        2. ...
    Average Code Errors Per Student: <number>

    Most ...
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
    print('===================== Statistics per Submission',
          '=====================')

    for name, stats in individual_stats.items():
        print('Submission by:', name)

        # Totals are printed differently
        header, totals = stats.pop(0)
        print('\t{}:'.format(header))
        for total, count in totals:
            print('\t\t{:26}{}'.format(total + ':', count))

        # Print "most frequent" stats
        for stat_type, results in stats:
            print('\t{}:'.format(stat_type))
            _print_top_errors(results, 2, False)
        print('\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n')

    if len(summary_stats) == 0:
        return

    print('\n================== Aggregate Statistics for Directory',
          '==================')

    # Most Frequent Code Errors
    stat_type, stats = summary_stats[0]
    print(stat_type + ':')
    _print_top_errors(stats)

    # Average Code Errors Per Student
    print('{}: {}\n'.format(summary_stats[1][0], summary_stats[1][1]))

    # Most Frequent Style Errors
    stat_type, stats = summary_stats[2]
    print(stat_type + ':')
    _print_top_errors(stats)

    # Average Style Errors Per Student
    print('{}: {}\n'.format(summary_stats[3][0], summary_stats[3][1]))

    # Most Frequent Errors of Either Type
    stat_type, stats = summary_stats[4]
    print(stat_type + ':')
    _print_top_errors(stats)

    # Average Errors of Either Type Per Student
    print('{}: {}\n'.format(summary_stats[5][0], summary_stats[5][1]))

    # Five Number Summary
    print('======= {} ======='.format(summary_stats[6][0]))
    five_numbers = summary_stats[6][1]
    for stat_type, value in five_numbers:
        print('\t{:21}{}'.format(stat_type + ':', value))

    # Standard Deviation
    print('\n{}: {}'.format(summary_stats[7][0], summary_stats[7][1]))


def _print_top_errors(stats, tabs=1, aggregate=True):
    """Pretty prints a list of most frequent errors and their counts.

    @param List[Tuple[str, int | Tuple]] stats: the errors & counts to print
    @param int tabs: the number of tabs to print before every line
    @param bool aggregate: whether stats are aggregate (i.e.: no percentages)
    @rtype: None
    """
    for i, stat in enumerate(stats):
        print('{}{}.'.format('\t' * tabs, i + 1), end=' ')
        # TODO: figure out a non-hardcoded alternative for 38 in prints:
        if aggregate:
            print('{:38} {:3}'.format(stat[0] + ':', stat[1]))
        else:
            print('{:38} {:3} ({}%)'.format(stat[0][0] + ':',
                                            stat[0][1], stat[1][1]))
