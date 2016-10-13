def indiv_calc(error_msgs, style_msgs):
    """
    Analyses the given lists of error and style Message objects error_msgs and
    style_msgs for an individual.

    @param list error_msgs: Message objects for all of a student's code errors
    @param list style_msgs: Message objects for all of a student's style issues
    @rtype: list[tuple]
    """

    # {msg.symbol + "(" + msg.object + ")": count}
    all_msgs = error_msgs + style_msgs

    all_num = _calc_helper(all_msgs)
    error_num = _calc_helper(error_msgs)
    style_num = _calc_helper(style_msgs)

    stats = [('Most Frequent Messages In Numbers', all_num[0]),
             ('Most Frequent Messages In Percentages', all_num[1]),
             ('Most Frequent Errors In Numbers', error_num[0]),
             ('Most Frequent Errors in Percentages', error_num[1]),
             ('Most Frequent Styles In Numbers', style_num[0]),
             ('Most Frequent Styles in Percentages', style_num[1])]

    return stats


def summary(all_msgs):
    """
    Provides a summary of each individual's errors from all_msgs and provide an
    overall summary of the course's performance (if applicable).
    Called by pyta_statistics.

    @param dict[str -> tuple(list[Message], list[Message])] all_msgs:
        the tuple of code and error messages for each student's files
    @rtype: list[list[tuple]]]
    """
    num_stu = len(all_msgs)

    # If directory was for student, not course, return empty summary stats list.
    if num_stu == 1:
        student, stats = all_msgs.popitem()
        return [[(student, indiv_calc(*stats))], []]

    sum_calc = [[], []]
    code_errors = []
    style_errors = []
    stu_errors = []

    for student in all_msgs:
        # in the form [('std1', [<stats>]), ('std2', [<stats>])]
        errors = all_msgs[student][0]
        styles = all_msgs[student][1]
        calc = indiv_calc(errors, styles)
        sum_calc[0].append((student, calc))
        stu_errors.append((len(errors) + len(styles), student))

        # To find Most Frequent Errors (aggregate)
        code_errors.append(errors)
        style_errors.append(styles)

    error_num = frequent_messages(_message_counter(code_errors))
    style_num = frequent_messages(_message_counter(style_errors))

    # Calculating the Five Number Summary for all errors (per student)
    stu_errors.sort(reverse=True)

    if len(stu_errors) == 1:
        median = stu_errors[0][0]
    elif len(stu_errors) % 2 == 1:
        median = stu_errors[len(stu_errors) // 2 + 1][0]
    else:
        median = (stu_errors[len(stu_errors) // 2 + 1][0] +
                  stu_errors[len(stu_errors) // 2])[0] // 2

    q3 = stu_errors[round(0.25 * len(stu_errors))]
    q1 = stu_errors[round(0.75 * len(stu_errors))]

    sum_calc[1] = [('Top 5 Frequent Code Errors', error_num),
                   ('Average Code Errors Per Student',
                    (len(code_errors) / num_stu).__round__(2)),
                   ('Top 5 Frequent Style Errors', style_num),
                   ('Average Style Errors Per Student',
                    (len(style_errors) / num_stu).__round__(2)),
                   ('Five Number Summary of Errors Per Student',
                    [('Most', stu_errors[0]),
                     ('Upper Quartile (Q3)', q3),
                     ('Median', median),
                     ('Lower Quartile (Q1)', q1),
                     ('Least', stu_errors[-1])])]

    return sum_calc


def _calc_helper(msgs):
    """
    Returns frequent messages in numbers and in percentages.

    @param list[Message] msgs: Message objects for all errors found by linters
    @rtype: list
    """
    # get dict of values {id:int, id2:int}
    msgs_dict = _message_counter(msgs)
    # sort into list of tuple, highest on top
    freq_nums = frequent_messages(msgs_dict)
    total_msgs = len(msgs)
    # divide each value by total and round to two places
    for message in msgs_dict:
        msgs_dict[message] = (msgs_dict[message]/total_msgs * 100).__round__(2)
    perc_nums = frequent_messages(msgs_dict)
    return [freq_nums, perc_nums]


def _message_counter(msgs):
    """
    Returns the number of errors for every type of error in msgs.

    @param list[Message] msgs: any given Message objects for errors
    @rtype: dict[str : int]
    """

    msgs = msgs.copy()  # prevent aliasing
    msgs_dict = {}

    for msg in msgs:
        key = msg.msg_id + " (" + msg.symbol + ")"
        if key not in msgs_dict:
            msgs_dict[key] = sum(1 for m in msgs if m.msg_id == msg.msg_id)
    return msgs_dict


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
