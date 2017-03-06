# Python TA Reporters TODOs

## `ColorReporter`

* Come up with a better solution than highlighting the whole error line for messages without `node` attributes:

    * `line-too-long`
    * `bad-whitespace`
    * `trailing-newlines`

* Consider a special code-snippet and highlight strategy for unusual messages such as:

    * `always-returning-in-a-loop`
    * `too-many-nested-blocks`

* The triple-nested functions for `print_messages` might be overkill - consider turning `add_line` into a regular method.

## `HTMLReporter`

* The source code on the output.html page currently does not have the correct indent. Fix the indentation so that the source code looks exactly like the original source code.

* Find a way to make the width of the white box (that shows the source code) corresponds with the longest line of the source code. Right now, if the lines of the source code aren't long, the right side of the white box looks empty, but if the lines are too long, the box doesn't fit the lines.

* Use javascript to expand and close the source code of each error messages.
