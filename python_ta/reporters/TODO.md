# Python TA Reporters TODOs

## `ColorReporter`

* Come up with a better solution than highlighting the whole error line for messages without `node` attributes:

    * `line-too-long`
    * `bad-whitespace`
    * `trailing-newlines`

* Consider a special code-snippet and highlight strategy for unusual messages such as:

    * `always-returning-in-a-loop`
    * `too-many-nested-blocks`

## `HTMLReporter`

* Not all error messages are explained on the website: http://www.cs.toronto.edu/~david/pyta/:

    * `C0305 (trailing-newlines)`

* Use javascript to expand and close the source code of each error messages.

* `python_ta.checkall()` does not work on all code now. An unexpected error occurs and returns **ERROR: last_child is missing or is missing attributes.** when we call python_ta.checkall() on the student's code (from Assignment 3). Also, the ColorReporter shows the correct output for pylint.W0631_undefined_loop_variable, but the HTMLReporter doesn't.
