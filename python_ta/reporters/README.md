# Python TA Reporters README

## ColorReporter

As of now, the ColorReporter has been configured to print out detailed
information on each code and style error message produced by PyTA.
As before, messages are separated into code errors and style errors, and
further sorted by type. The new ColorReporter colour-codes these
messages, using red for code error messages (and error codes) and blue
for style error messages (and error codes).<sup>1</sup>

Each message (regardless of type) is presented as several pieces of
information about the message and its cause. In the current version of
ColorReporter, messages of the same type are no longer merged together
but are instead shown each with their individual highlighted code snippet
(if applicable), although they are bundled under a common heading.

The format of a typical ColorReporter result:

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
them are formatted thus: each line is composed of 4 spaces, the right-
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
subject to change in later versions of the ColorReporter.

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
Although we have designed the ColorReporter to print using these colours, our use of
`colorama` and ANSI character sequences to effect this change means that the actual
colour that will be seen by users will vary from terminal to terminal, since every console
makes its own decisions as to how to present ANSI colour codes. In light of this, we have
endeavoured to choose our colour scheme in such a way as to be compatible with a variety
of terminals and terminal colour themes (for example, our coloured text has been checked
for legibility in every _builtin_ PyCharm colour scheme), but we are unable to ensure
compatibility with every custom colour scheme. If your PyTA messages are not visible,
please consider changing your theme.</small>

<small><sup>2</sup> **Note on code highlighting:**
As ColorReporter is dependent on other PyTA elements for highlighting the correct part of a
line of code, and those elements are still buggy, expect some problems with the highlighting the
exact location of a problem. For more details, please see the [TODO list](TODO.md), as well as the known
bug reports for the `setendings` module.</small>

## HTMLReporter

The HTMLReporter outputs an HTML file, `output.html`, that shows very
similar content as the current ColorReporter. The `output.html` file was
located in the parent pyta directory before, but it is now located in
pyta/python_ta/reporters/templates. `output.html` is opened in a browser when
a user calls `python_ta.check_all()` with the HTMLReporter. A statement is also
printed in the console to inform the user that a browser is opening:

```
Opening your report in a browser...

```

The HTMLReporter is no longer a subclass of the PlainReporter. It is
now a subclass of the ColorReporter as it uses the exact same methods as the
ColorReporter in order to output the same coloured content as the ColorReporter.
Note that in the ColorReporter, `_add_line()` and `_colourify()` are implemented
to handle both python syntax and HTML syntax.

A CSS file, `stylesheet.css`, is located in pyta/python_ta/reporters/templates,
and is linked to `template.txt`. The `output.html` file is no longer a plain black
and white page. A title, "PyTA Error Report", is at the top centre of the page.
The error messages are shown in a white box in the centre of the page, and
have the same font colours and highlight colours as the ColorReporter.
The fonts are Lucida Console with monospace as the backup or Lucida Console
with sans serif as the backup.

The theme colour of the web page is blue. The background colour
and the font colour of the title are in different shades of blue. The date and
time are at the top right corner; however, more work might be done on it. Please
see the [TODO list](TODO.md) for more details. If the user clicks on the error
message symbol, the user will be redirected to the location of the error message
on the PyTA documentation website. For example, if the user has an error message,
`W0612 (unused-variable) Number of occurrences: 1`, and clicks on `W0612(unused-variable)`,
the user will be redirected to http://www.cs.toronto.edu/~david/pyta/#W0612. A
PyTA logo is located at the bottom of the web page and also redirects the user to
the PyTA documentation website on click. Slightly above the logo, there is a link
that allows users to report bugs via email.


### Technical Details

In order for the `template.txt` to have access to the coloured and sorted error
messages, we added an attribute, `snippet`, to NewMessage on line 5 in the PlainReporter.
In `stylesheet.css`, there are several classes that set the font and the
colour of certain text. The class attributes in the HTMLReporter, self.\_space
and self.\_colouring, override the ones in the ColorReporter so that `snippet`
is constructed in HTML syntax and can be directly printed by the `template.txt`.
Each element in self.\_colouring corresponds to one of the classes in `stylesheet.css`.
The `template.txt` simply shows the resulted error messages by printing the
`snippet` attribute of each message.
