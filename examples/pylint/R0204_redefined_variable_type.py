def obvious_variable_redefinition(arg):
    """Redefinition of <variable-name> type from <type_1> to <type_2>"""
    arg = 1
    arg = 'string'  # Redefinition of var type from int to str


def other_redefinition_example(arg):
    """Redefinition of <variable-name> type from <type_1> to <type_2>"""
    if arg == 3:
        var = 'eight'
    else:
        var = 8  # Redefinition of var type from str to int
