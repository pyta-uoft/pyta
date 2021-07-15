# Configuration

```{note}
This page is current under construction!
```

## Reporters

PythonTA offers four different types of *reporters* used to display the results of its checks to the user.

- `python_ta.reporters.PlainReporter`: outputs report in plain text.
- `python_ta.reporters.ColorReporter`: outputs a colourized report (can only be used in the terminal/Python shell)
- `python_ta.reporters.HTMLReporter`: outputs report in HTML format.
- `python_ta.reporters.JSONReporter`: outputs a JSON representation of the messages reported

The default reporter is HTMLReporter.
This is controlled by the `output-format` configuration option, which you can set in a call to `python_ta.check_all` or in your `.pylintrc` file.

```python
import python_ta
python_ta.check_all(..., config={'output-format': 'python_ta.reporters.PlainReporter'})
```

```toml
[REPORTS]
output-format = python_ta.reporters.PlainReporter
```

### Report output location

By default, the PlainReporter, ColorReporter, and JSONReporter print their reports to the screen,
and the HTMLReporter opens a web browser to display the report.
You can instead configure PythonTA to save the reports to a file using the `output` argument to `check_all`:

```python
import python_ta
python_ta.check_all(..., output='pyta_output.txt')
```

This options is compatible with all of PythonTA's reporter types, but we do not recommend its use with ColorReporter,
as this reporter uses terminal-specific characters to colourize text displayed on your screen.
