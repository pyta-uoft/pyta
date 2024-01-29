# Configuration

```{note}
This page is currently under construction!
```

## Providing Your Own Configuration Settings

While PythonTA comes with its own default configuration settings, you can provide either a `dict` or the file name of the config file containing the configuration options you want to override. PythonTA will use its default options for all other options.

When providing your own configuration settings as a file, you just need to provide a minimal configuration file that contains only the configuration options you wish to override. The configuration file must be in the [TOML](https://toml.io/en/v1.0.0) file format.

### Sample Usage

```python
import python_ta

options = {
    'pyta-number-of-messages': 10,
    'max-line-length': 100,
    ...,
}

# Using config dict
python_ta.check_all(..., config=options)

# Using config file
# Assume there is a config file `config/.pylintrc`
python_ta.check_all(..., config='config/.pylintrc')
```

```ini
# config/.pylintrc
[CUSTOM PYTA OPTIONS]
pyta-number-of-messages = 10

[FORMAT]
max-line-length = 100

...
```

### Autoloading PythonTA default config

The `load_default_config` option of `check_errors` and `check_all` can be used to specify whether to automatically load the PythonTA default config. By default, PythonTA will automatically load the default config.

When disabled, it will still load PythonTA's custom options, but will no longer override pylint's default options. As such, it will use pylint's default options.

```python
import python_ta

python_ta.check_all(..., load_default_config=False)
```

## Allowing 'pylint:' Comments

PythonTA allows you to choose whether you want to locally disable checks by using 'pylint:' in a comment, i.e. it
lets you choose whether or not you want to allow comments that begin with 'pylint:'. The default value for this option is False, i.e. PythonTA by default would not allow you to use 'pylint:' in a comment.

```python
import python_ta

python_ta.check_all(..., config={"allow-pylint-comments": True})
```

## Custom Error Messages

By default, PythonTA overwrites some of pylint's error messages with its own to make them more beginner-friendly.
These messages are specified in `config/messages_config.toml` in the source code. You can prevent this by setting the
`use-pyta-error-messages` option to `False`.

```python
import python_ta
python_ta.check_all(config={
    "use-pyta-error-messages": False
})
```

PythonTA also allows for pylint error messages to be overridden with custom user messages.
The user can provide their own messages configuration file by specifying `messages-config-path` in their `.pylintrc` file.
These messages have priority over both pylint's and PythonTA's messages and aren't affected by `use-pyta-error-messages`.

## Reporters

PythonTA offers four different types of _reporters_ used to display the results of its checks to the user.

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

```ini
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

## Forbidden Imports

By default, PythonTA has a list of modules that are allowed to be imported. You can specify any additional modules using the `extra-imports` configuration option, which you can set in a call to `python_ta.check_all` or in a configuration file.

```python
import python_ta
python_ta.check_all(..., config={'extra-imports': ["math", "tkinter"]})
```

```ini
[FORBIDDEN IMPORT]
extra-imports = math, tkinter
```

In addition, you can specify `allow-local-imports` to allow local imports.

```python
import python_ta
python_ta.check_all(..., config={'allow-local-imports': True})
```

```ini
[FORBIDDEN IMPORT]
allow-local-imports = yes
```
