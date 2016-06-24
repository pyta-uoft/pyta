def obvious_variable_redefinition(arg):
    """Redefinition of <variable-name> type from <type_1> to <type_2>"""
    arg = 1
    arg = "string"  # redefined variable type


def other_redefinition_example(arg):
    """Redefinition of <variable-name> type from <type_1> to <type_2>"""
    if arg == 3:
        var = "eight"
    else:
        var = 8  # redefined variable type
