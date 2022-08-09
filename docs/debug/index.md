# Loop Debugging

This page describes an additional PythonTA feature: print-based loop debugging.
This feature makes it easier to trace the execution of a for loop by printing the state of each loop iteration in a nicely-formatted table using the [tabulate] library.

## Example usage

This feature uses the `python_ta.debug.AccumulationTable` as a context manager wrapping a for loop.
Here is a complete example of its use:

```python
# demo.py
from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers.
    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"]):
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    return list_so_far


if __name__ == '__main__':
    calculate_sum_and_averages([10, 20, 30, 40, 50, 60])
```

When this file is run, we get the following output:

```console
$ python demo.py
iteration    number    sum_so_far    avg_so_far    list_so_far
-----------  --------  ------------  ------------  ---------------------------------------------------------------------------
0            N/A       0             None          []
1            10        10            10.0          [(10, 10.0)]
2            20        30            15.0          [(10, 10.0), (30, 15.0)]
3            30        60            20.0          [(10, 10.0), (30, 15.0), (60, 20.0)]
4            40        100           25.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0)]
5            50        150           30.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0)]
6            60        210           35.0          [(10, 10.0), (30, 15.0), (60, 20.0), (100, 25.0), (150, 30.0), (210, 35.0)]
```

## API

```{eval-rst}
.. automethod:: python_ta.debug.AccumulationTable.__init__
```

The `AccumulationTable` class has the following instance attributes you can access after the `with` statement.

```{eval-rst}
.. autoattribute:: python_ta.debug.AccumulationTable.loop_variables

.. autoattribute:: python_ta.debug.AccumulationTable.loop_accumulators
```

For example:

```python
from python_ta.debug import AccumulationTable


def calculate_sum_and_averages(numbers: list) -> list:
    """Return the running sums and averages of the given numbers.
    """
    sum_so_far = 0
    list_so_far = []
    avg_so_far = None
    with AccumulationTable(["sum_so_far", "avg_so_far", "list_so_far"]) as table:
        for number in numbers:
            sum_so_far = sum_so_far + number
            avg_so_far = sum_so_far / (len(list_so_far) + 1)
            list_so_far.append((sum_so_far, avg_so_far))

    print(table.loop_accumulators)
    return list_so_far

```

## Current limitations

The `AccumulationTable` is a new PythonTA feature and currently has the following known limitations:

1. `AccumulationTable` uses [`sys.settrace`] to update variable state, and so is not compatible with other libraries (e.g. debuggers, code coverage tools).

2. Does not have support for while loops

3. Only supports loop accumulation variables, but not accumulators as part of an object.
   For example, instance attribute accumulators are not supported:

   ```python
   class MyClass:
       def update_my_sum(self, numbers):
           for number in numbers:
               self.sum_so_far = self.sum_so_far + number
   ```

4. Loop variable state is stored by creating shallow copies of the objects.
   Loops that mutate a nested part of an object will not have their state displayed properly.

5. All tracked loop variables other than the for loop target must be initialized before the loop,
   even when the variables are guaranteed to be initialized before use inside the loop body.

6. The `AccumulationTable` context manager can only log the execution of one for loop.
   To log the state of multiple for loops, each must be wrapped in a separate `with` statement and fresh `AccumulationTable` instance.

[tabulate]: https://github.com/astanin/python-tabulate
[`sys.settrace`]: https://docs.python.org/3/library/sys.html#sys.settrace
