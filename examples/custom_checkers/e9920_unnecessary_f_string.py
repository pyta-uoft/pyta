"""Examples for e9920_unnecessary_f_string_checker """


def demo_function() -> str:
    """
    Demonstrates e9920_unnecessary_f_string_checker
    """
    x = "hello"
    a = f"{x}"  # error on this line

    b = f"{x =}"  #no error open

    c = f"{x + ' world'}"  # error on this line

    return x + a + c
