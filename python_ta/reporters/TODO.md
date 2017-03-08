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

* Find a way to make the width of the white box (that shows the source code) corresponds with the longest line of the source code. Right now, if the lines of the source code aren't long, the right side of the white box looks empty, but if the lines are too long, the box doesn't fit the lines.

* Not all error messages are explained on the website: http://www.cs.toronto.edu/~david/pyta/:

    * `C0305 (trailing-newlines)`

* Use javascript to expand and close the source code of each error messages.

* `python_ta.checkall()` does not work on all examples. An unexpected error occurs and returns **Got unexpected field names: ['snippet']** when `python_ta.check_all("examples.pylint.W0631_undefined_loop_variable", reporter=HTMLReporter)` or `python_ta.check_all("examples.pylint.W0631_undefined_loop_variable")` is called. This is most likely because we added a new attribute, **snippet**, to **NewMessage** in the PlainReporter.

* When the user opens the output.html for the first time, the date at the top right corner is the time when the output.html file is created. It, however, changes to the current time if the user refreshes the page. Find a way to prevent the date and time from changing after page refresh.

* Show the file name.
