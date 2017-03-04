# Python TA Reporters README

## `ColorReporter`

As of now, the `ColorReporter` has been configured to print out detailed
information on each code and style error message produced by PyTA.
As before, message are separated into code errors and style errors, and
further sorted by type. The new `ColorReporter` colour-codes these
messages, using red for code error messages (and error codes) and blue
for style error messages (and error codes).<sup>1</sup>

Each message (regardless of type) is presented as several pieces of
information about the message and its cause. In the current version of
`ColorReporter`, messages of the same type are no longer merged together
but are instead shown each with their individual highlighted code snippet
(if applicable), although they are bundled under a common heading.

The format of a typical `ColorReporter` result:

```
=== Message Type (Code or Style) Heading ===
MessageCode (MessageSymbol)  Number of occurrences: ___.

    [Line __] First Message Instance Message

    Your Code Starts Here:

    ...    ..........

    [Line __] Second Message Instance Message

    Your Code Starts Here:

    ...    ..........

```


### Technical Details

Please note that _not all_ messages are accompanied by a code snippet.
However, for those interested, the code snippets of messages that have
them  are formatted thus: each line is composed of 4 spaces, the right-
aligned (up to 3 digits of padding) line number, another 4 spaces, and
the line of source code, with original indenting preserved and the relevant
part of the line highlighted (if the error appears on that line).<sup>2</sup> The default
error highlight colour is black text on a cyan background.<sup>1</sup>
Short code snippets (less than 4 lines) are preceded and proceeded by
up to 2 greyed-out lines of surrounding code for context.

#### Special Messages

Most messages are accompanied by a code snippet highlighted according
to their `msg.node`'s `fromlineno`, `end_lineno`, `col_offset`, and `end_col_offset`
attributes. In absence of these attributes, or for messages for which a code
snippet is nonsensical or cumbersome, other actions have been taken.
The following is the current list of "special" messages; they may be
subject to change in later versions of the `ColorReporter`.

Messages that always highlight the whole error line<sup>2</sup> (sorted by message symbol):

* `bad-whitespace`
* `line-too-long`
* `trailing-newlines`

Messages that treat code snippets differently than just printing/highlighting:

* `Missing function docstring` subtype of `missing-docstring`
    * For these messages, the first line of the code snippet (the function
        definition) is printed and highlighted, followed by a single elided
        line (`...`) to signify the rest of the function/the missing docstring.

Messages that omit code snippets altogether:

* `missing-docstring` (except the `Missing function docstring` subtype)
* `always-returning-in-a-loop`
* `too-many-nested-blocks`
* `invalid-name` (but only the `Invalid module name` subtypes)

- - -

##### Notes

<small><sup>1</sup> **Note on the colour scheme:**
Although we have designed the `ColorReporter` to print using these colours, our use of
`colorama` and ANSI character sequences to effect this change means that the actual
colour that will be seen by users will vary from terminal to terminal, since every console
makes its own decisions as to how to present ANSI colour codes. In light of this, we have
endeavoured to choose our colour scheme in such a way as to be compatible with a variety
of terminals and terminal colour themes (for example, our coloured text has been checked
for legibility in every _builtin_ PyCharm colour scheme), but we are unable to ensure
compatibility with every custom colour scheme. If your PyTA messages are not visible,
please consider changing your theme.</small>

<small><sup>2</sup> **Note on code highlighting:**
As `ColorReporter` is dependent on other PyTA elements for highlighting the correct part of a
line of code, and those elements are still buggy, expect some problems with the highlighting the
exact location of a problem. For more details, please see the [TODO list](TODO.md), as well as the known
bug reports for the `setendings` module.</small>

## `HTMLReporter`

To be added.
