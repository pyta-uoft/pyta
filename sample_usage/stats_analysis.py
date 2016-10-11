from .pyta_stats import frequent_messages


def stats_calculator(error_msgs, style_msgs):  # these two things will be lists of Message objects
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
    msgs_dict = message_counter(all_msgs)
    # sort into list of tuple, highest on top
    freq_nums = frequent_messages(msgs_dict)

    total_errors = sum([msgs_dict[msg_id] for msg_id in msgs_dict])
    # divide each value by total and round to two places
    for message in msgs_dict:
        msgs_dict[message] = (msgs_dict[message]/total_errors * 100).__round__(2)
    perc_nums = frequent_messages(msgs_dict)
    stats = {'Most Frequent Messages In Numbers': freq_nums,
             'Most Frequent Messages In Percentages': perc_nums}

    return stats

    # return dict = {"error" : int}


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
