# PythonTA Additional Debugging Features

This page describes in greater detail the additional debugging features that
PythonTa has to offer. If anything is unclear, incorrect, or missing, please don't hesitate to send an
email to \[david at cs dot toronto dot edu\].

## Printed Accumulation Table

This feature allows the output of each loop iteration to be printed
nicely in table format.

For example:

```python
def my_func(numbers: list) -> tuple:
    """Return the sum and average at each iteration
    of the numbers in numbers.

    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = 'N/A'
    for number in numbers:
        sum_so_far = sum_so_far + number
        avg_so_far = sum(list_so_far) / len(list_so_far)
        list_so_far.append(avg_so_far)

    return (sum_so_far, list_so_far)
```

Table output:

```
iterations    loop variable (number)    sum_so_far    list_so_far               avg_so_far
------------  ------------------------  ------------  ------------------------  ------------
0             N/A                       0             []                        N/A
1             10                        10            [10]                      10.0
2             20                        30            [10, 20]                  15.0
3             30                        60            [10, 20, 30]              20.0
4             40                        100           [10, 20, 30, 40]          25.0
5             50                        150           [10, 20, 30, 40, 50]      30.0
6             60                        210           [10, 20, 30, 40, 50, 60]  35.0
```
