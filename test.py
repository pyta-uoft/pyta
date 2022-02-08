# demo.py
def test(x: int, y: int) -> int:
    """
    Preconditions:
        - y < 10
        - y < 100
        - y < 1000
        - y < 10
        - y < 100
        - y < 1000
        - y < 10
        - y < 100
        - y < 1000
        - y < 10
        - y < 100
        - y < 1000
        - y < 10
        - y < 100
        - y < 1000
    """
    return x + y

def run_test():
    from python_ta.contracts import check_all_contracts
    check_all_contracts()
    for i in range(0, 1000):
        test(10, i)


if __name__ == '__main__':
    import timeit
    run_test()