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

* Fix the file name in the header (use CSS `float` properly).
