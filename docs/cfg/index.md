# Control Flow Graphs

This page describes an additional PythonTA feature: visualizing the control flow of a program.
This feature makes it easier to visualize how the computer executes your program by producing a scalable control flow graph using the [graphviz] library.

## Sample Usage

This feature uses `python_ta.cfg.generate_cfg` to produce these control flow graphs.

The first argument specifies which Python file to create a control flow graph for. By default, it generates a control flow graph of the current file in which it is called from.

```python
... # code here

if __name__ == "__main__":
    import python_ta.cfg

    python_ta.cfg.generate_cfg()
```

This feature is not limited to just the Python file containing the function call. It can also be used to generate a control flow graph of a different Python file. The set-up is the exact same as before, except we can pass an argument to the function call which is the path (relative or absolute) of the target Python file.

```python
... # same as before

python_ta.cfg.generate_cfg(<path of Python file>)
```

In addition, the second argument can be used to choose whether or not to display the control flow graph immediately after creating it. By default, it will automatically display the control flow graph after creating it.

```python
...  # same as before

python_ta.cfg.generate_cfg(..., True)  # Displays the cfg in your browser

python_ta.cfg.generate_cfg(..., False)  # Creates the graph but won't display it
```

## API

```{eval-rst}
.. autofunction:: python_ta.cfg.generate_cfg
```

## Current Limitations

1. Various Python syntax such as Raise statements and for loops aren't labelled.

2. Only one control flow graph can be generated per function call (i.e. you can't pass in a list of files to generate control flow graphs for).

[graphviz]: https://github.com/graphp/graphviz
