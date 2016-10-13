from .pyta_stats import frequent_messages


def indiv_calc(error_msgs, style_msgs):  # these two things will be lists of Message objects
    """
    Analyse the given lists of error and style Message objects error_msgs and
    style_msgs for an individual.
    Called by StatReporter.

    @param list error_msgs: Message objects for all errors found by linters
    @param list style_msgs: Message objects for all style issues
    @rtype: list[tuple]
    """

    # {msg.symbol + "(" + msg.object + ")": count}
    all_msgs = error_msgs + style_msgs

    all_num = calc_helper(all_msgs)
    error_num = calc_helper(error_msgs)
    style_num = calc_helper(style_msgs)

    stats = [('Most Frequent Messages In Numbers', all_num[0]),
             ('Most Frequent Messages In Percentages', all_num[1]),
             ('Most Frequent Errors In Numbers', error_num[0]),
             ('Most Frequent Errors in Percentages',error_num[1]),
             ('Most Frequent Styles In Numbers', style_num[0]),
             ('Most Frequent Styles in Percentages', style_num[1])]

    return stats

def summary(all_msgs):
    """
    Provide a summary of each individual's errors from all_msgs and provide an
    overall summary of the class's performance.

    :param list[Message]:
    :rtype: list[list[tuple]]]
    """
    sum_calc = [[],[]]
    num_stu = len(all_msgs)
    code_errors = 0
    style_errors = 0
    total_errors = code_errors + style_errors
    freq_error = {}
    freq_style = {}

    for student in all_msgs:
        # in the form [('std1', [<stats>]), ('std2', [<stats>])]
        errors = all_msgs[student][0]
        styles = all_msgs[student][1]
        calc = indiv_calc(errors, styles)
        sum_calc[0].append((student, calc))
        # to find Most Frequent Errors in Numbers
        for code_error in calc[2][1]:
            # in ('msg.id', 3), ('msg.id2', 2) format currently
            code_errors += code_error[1] # add 3 and 2 for above example
            if code_error not in freq_error:
                freq_error[code_error] = code_error[1]
            else:
                freq_error[code_error] += code_error[1]
        # to find Most Frequent Styles in Numbers
        for style_error in calc[4][1]:
            style_errors += style_error[1]
            if style_error not in freq_style:
                freq_style[style_error] = style_error[1]
            else:
                freq_style[style_error] += style_error[1]

    error_numperc = calc_helper(freq_error)
    style_numperc = calc_helper(freq_style)


    sum_calc[1].append((('Top 3 Frequent Code Errors', (error_numperc[0][:3], error_numperc[1][:3]),
                        ('Average Code Errors Per Student',
                         code_errors/num_stu.__round__(2)),
                        ('Top 3 Frequent Style Errors', (style_numperc[0][:3], error_numperc[1][:3])),
                        ('Average Style Errors Per Student',
                         style_errors/num_stu.__round__(2)))))

    return sum_calc


def calc_helper(msgs):
    """
    Returns frequent messages in numbers and in percentages.

    :param list[Message]: Message objects for all errors found by linters
    :rtype: list
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
