# Python TA Reporters TODOs

## `ColorReporter`

* Come up with a better solution than highlighting the whole error line for messages without `node` attributes:

    * `line-too-long`
    * `bad-whitespace`
    * `trailing-newlines`

* Consider a special code-snippet and highlight strategy for unusual messages such as:

    * `always-returning-in-a-loop`
    * `too-many-nested-blocks`

* In the vaguely distant future, when more people reliably have Python 3.6,
  change the ints in the LineType class definition into `enum.auto()` calls.
    * (will need to be imported, of course)

## `HTMLReporter`

* Fix the following `_COLOURING` dict entries, which need to be included so that HTMLReporter can call `_colour_messages_by_type` safely (currently useless):
    * 'bold', 'code-heading', 'style-heading', 'code-name', 'style-name'

* Use javascript to expand and close the source code of each error messages.

* The ColorReporter shows the correct output for pylint.W0631_undefined_loop_variable, but the HTMLReporter doesn't.

## Other

* Consider changing ColorReporter & HTMLReporter's `_COLOURING` dict to an Enum.

* Not all error messages are explained on the website: http://www.cs.toronto.edu/~david/pyta/:

    * `C0305 (trailing-newlines)`

* `python_ta.check_all()` does not work on all code now. An unexpected error occurs and returns **ERROR: last_child is missing or is missing attributes.** when we call `python_ta.check_all()` on the student's code (from Assignment 3).
