def infinite_loop_basic() -> None:
    """An infinite while loop due to unused condition variables."""
    i = 0
    j = 100
    lst = [1, 2, 3]
    while i < 100 and lst[1] > 0:
        j -= 1  # 'i' and 'lst' are never updated


def infinite_loop_attribute_variable() -> None:
    """An infinite loop involving an attribute used in the condition."""
    class Demo:
        def __init__(self) -> None:
            self.var = 1

        def demo_method(self) -> None:
            var = 0
            while 0 < self.var < 100:
                var += 1  # 'self.var' is never updated
    Demo().demo_method()
