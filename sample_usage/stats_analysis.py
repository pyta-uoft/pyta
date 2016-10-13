from .pyta_stats import frequent_messages


def indiv_calc(error_msgs, style_msgs):  # these two things will be lists of Message objects
    """
    Analyse the given lists of error and style Message objects to aggregate
    statistics on and return them in dictionary form.
    Called by StatReporter.

    @param list error_msgs: Message objects for all errors found by linters
    @param list style_msgs: Message objects for all style issues
    @rtype: dict
    """

    # {msg.symbol + "(" + msg.object + ")": count}
    all_msgs = error_msgs + style_msgs

    all_num = calc_helper(all_msgs)
    error_num = calc_helper(error_msgs)
    style_num = calc_helper(style_msgs)

    stats = {'Most Frequent Messages In Numbers': all_num[0],
             'Most Frequent Messages In Percentages': all_num[1],
             'Most Frequent Errors In Numbers': error_num[0],
             'Most Frequent Errors in Percentages':error_num[1],
             'Most Frequent Styles In Numbers': style_num[0],
             'Most Frequent Styles in Percentages': style_num[1]}

    return stats

    # return dict = {"error" : int}

def summary_calc(all_msgs):
    """

    :param list[Message]:
    :rtype: list
    """
    pass

def calc_helper(msgs):
    """
    Returns frequent messages in numbers and in percentages.

    :param list[Message]: Message objects for all errors found by linters
    :rtype: list
    """
    # get dict of values {id:int, id2:int}
    msgs_dict = message_counter(msgs)
    # sort into list of tuple, highest on top
    freq_nums = frequent_messages(msgs_dict)
    total_msgs = sum([msgs_dict[msg_id] for msg_id in msgs_dict])
    # divide each value by total and round to two places
    for message in msgs_dict:
        msgs_dict[message] = (msgs_dict[message]/total_msgs * 100).__round__(2)
    perc_nums = frequent_messages(msgs_dict)
    return [freq_nums, perc_nums]


def message_counter(msgs):
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
