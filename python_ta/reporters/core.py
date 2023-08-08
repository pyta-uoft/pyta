"""This module provides the core functionality for all PythonTA reporters.
"""
import os.path
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from astroid import NodeNG
from pylint.message import Message
from pylint.message.message_definition import MessageDefinition
from pylint.reporters import BaseReporter
from pylint.reporters.ureports.nodes import BaseLayout

from .node_printers import LineType, render_message


class NewMessage:
    """Extension of Pylint's Message class to incorporate astroid node and source code snippet."""

    def __init__(self, message: Message, node: NodeNG, snippet: Optional[str]) -> None:
        self.message = message
        self.node = node
        self.snippet = snippet

    def __getattr__(self, item):
        return getattr(self.message, item)

    def to_dict(self) -> Dict:
        """Return a dictionary containing the fields of this message.

        Useful for JSON output.
        """
        return {
            **vars(self.message),
            "snippet": self.snippet,
            # The following are DEPRECATED and will be removed in a future release.
            "line_end": self.message.end_line,
            "column_end": self.message.end_column,
        }


# Messages without a source code line to highlight
NO_SNIPPET = {
    "invalid-name",
    "unknown-option-value",
    "module-name-violation",
    "config-parse-error",
    "useless-option-value",
    "unrecognized-option",
}


class PythonTaReporter(BaseReporter):
    """Abstract superclass for all PythonTA reporters.

    Reminder: see pylint BaseReporter for other instance variables.
    """

    # Rendering constants
    _SPACE = " "
    _BREAK = "\n"
    _COLOURING = {}
    _PRE_LINE_NUM_SPACES = 2

    # The error messages to report, mapping filename to a list of messages.
    messages: Dict[str, List[Message]]

    def __init__(self) -> None:
        """Initialize this reporter."""
        super().__init__()
        self.messages = defaultdict(list)
        self.source_lines = []
        self.module_name = ""
        self.current_file = ""

    def print_messages(self, level: str = "all") -> None:
        """Print messages for the current file.

        If level == 'all', both errors and style errors are displayed. Otherwise,
        only errors are displayed.
        """

    def has_messages(self) -> bool:
        """Return whether there are any messages registered."""
        return any(messages for messages in self.messages.values())

    def set_output(self, filepath: Optional[str] = None) -> None:
        """Set output stream based on filepath.

        If filepath is None or '-', sys.stdout is used.
        If filepath is the path to a file, that file is used (overwriting any existing contents).
        If filepath is the path to a directory, a new file is created in that directory
        (with default filename self.OUTPUT_FILENAME).
        """
        if filepath is None or filepath == "-":
            self.out = sys.stdout
        else:
            # Paths may contain system-specific or relative syntax, e.g. `~`, `../`
            filepath = os.path.expanduser(filepath)
            if os.path.isdir(filepath):
                filepath = os.path.join(filepath, self.OUTPUT_FILENAME)

            self.out = open(filepath, "w", encoding="utf-8")

    def handle_message(self, msg: Message) -> None:
        """Handle a new message triggered on the current file."""
        self.messages[self.current_file].append(msg)

    def handle_node(self, msg_definition: MessageDefinition, node: NodeNG) -> None:
        """Add node attribute to most recently-added message.

        This is used by our patched version of MessagesHandlerMixIn.add_message
        (see python_ta/patches/messages.py).
        """
        curr_messages = self.messages[self.current_file]
        if len(curr_messages) >= 1 and curr_messages[-1].msg_id == msg_definition.msgid:
            msg = curr_messages[-1]

            if msg.symbol in NO_SNIPPET or msg.msg.startswith("Invalid module"):
                snippet = ""
            else:
                snippet = self._build_snippet(msg, node)

            curr_messages[-1] = NewMessage(msg, node, snippet)

    def group_messages(
        self, messages: List[Message]
    ) -> Tuple[Dict[str, List[Message]], Dict[str, List[Message]]]:
        """Group messages for the current file by their (error/style) and type (msg_id)."""
        error_msgs_by_type = defaultdict(list)
        style_msgs_by_type = defaultdict(list)
        for msg in messages:
            if msg.msg_id in ERROR_CHECKS or msg.symbol in ERROR_CHECKS:
                error_msgs_by_type[msg.msg_id].append(msg)
            else:
                style_msgs_by_type[msg.msg_id].append(msg)

        return error_msgs_by_type, style_msgs_by_type

    def display_messages(self, layout: BaseLayout) -> None:
        """Hook for displaying the messages of the reporter

        This will be called whenever the underlying messages
        needs to be displayed. For some reporters, it probably
        doesn't make sense to display messages as soon as they
        are available, so some mechanism of storing them could be used.
        This method can be implemented to display them after they've
        been aggregated.
        """

    # Rendering
    def _build_snippet(self, msg: Message, node: NodeNG) -> str:
        """Return a code snippet for the given Message object, formatted appropriately according
        to line type.
        """
        code_snippet = ""

        for lineno, slice_, line_type, text in render_message(msg, node, self.source_lines):
            code_snippet += self._add_line(lineno, line_type, slice_, text)

        return code_snippet

    def _add_line(self, lineno: int, linetype: LineType, slice_: slice, text: str = "") -> str:
        """Format given source code line as specified and return as str.

        Called by _build_snippet, relies on _colourify.
        """
        snippet = self._add_line_number(lineno, linetype)

        if linetype == LineType.ERROR:
            start_col = slice_.start or 0
            end_col = slice_.stop or len(text)

            if text[:start_col]:
                snippet += self._colourify("black", text[:start_col])
            snippet += self._colourify("highlight", text[slice_])
            if text[end_col:]:
                snippet += self._colourify("black", text[end_col:])
        elif linetype == LineType.CONTEXT:
            snippet += self._colourify("grey", text)
        elif linetype == LineType.OTHER:
            snippet += text
        elif linetype == LineType.DOCSTRING:
            space_c = len(text) - len(text.lstrip(" "))
            snippet += space_c * self._SPACE
            snippet += self._colourify("highlight", text.lstrip(" "))

        snippet += self._BREAK
        return snippet

    def _add_line_number(self, lineno: int, linetype: LineType) -> str:
        """Return a formatted string displaying a line number."""
        pre_spaces = self._PRE_LINE_NUM_SPACES * self._SPACE
        spaces = 2 * self._SPACE
        if lineno is not None:
            number = "{:>3}".format(lineno)
        else:
            number = 3 * self._SPACE

        if linetype == LineType.ERROR:
            return pre_spaces + self._colourify("gbold-line", number) + spaces
        elif linetype == LineType.CONTEXT:
            return pre_spaces + self._colourify("grey-line", number) + spaces
        elif linetype == LineType.OTHER:
            return pre_spaces + self._colourify("grey-line", number) + spaces
        elif linetype == LineType.DOCSTRING:
            return pre_spaces + self._colourify("black-line", number) + spaces
        else:
            return pre_spaces + number + spaces

    def _display(self, layout: BaseLayout) -> None:
        """display the layout"""

    @classmethod
    def _colourify(cls, colour_class: str, text: str) -> str:
        """Return a colourized version of text, using colour_class.

        By default, returns the text itself.
        """
        return text

    # Event callbacks
    def on_set_current_module(self, module: str, filepath: Optional[str]) -> None:
        """Hook called when a module starts to be analysed."""
        # First, check if `module` is the name of a config file and if so, make filepath the
        # corresponding path to that config file.
        possible_config_path = Path(os.path.expandvars(module)).expanduser()

        if possible_config_path.exists() and filepath is None:
            filepath = str(possible_config_path)

        # Skip if filepath is None
        if filepath is None:
            return

        self.module_name = module
        self.current_file = filepath

        if self.current_file not in self.messages:
            self.messages[self.current_file] = []

        with open(filepath, encoding="utf-8") as f:
            self.source_lines = [line.rstrip("\r\n") for line in f.readlines()]

    def on_close(self, stats, previous_stats):
        """Hook called when a module finished analyzing.

        Close the reporter's output stream (if not sys.stdout).
        """
        if self.out is not sys.stdout:
            self.out.close()


# Checks to enable for basic_check (trying to find errors
# and forbidden constructs only)
ERROR_CHECKS = {
    "used-before-assignment",
    "undefined-variable",
    "undefined-loop-variable",
    "not-in-loop",
    "return-outside-function",
    "duplicate-key",
    "unreachable",
    "pointless-statement",
    "pointless-string-statement",
    "no-member",
    "not-callable",
    "assignment-from-no-return",
    "assignment-from-none",
    "no-value-for-parameter",
    "too-many-function-args",
    "invalid-sequence-index",
    "invalid-slice-index",
    "invalid-unary-operand-type",
    "unsupported-binary-operation",
    "unsupported-membership-test",
    "unsubscriptable-object",
    "unbalanced-tuple-unpacking",
    "unpacking-non-sequence",
    "function-redefined",
    "duplicate-argument-name",
    "import-error",
    "no-name-in-module",
    "non-parent-init-called",
    "access-member-before-definition",
    "method-hidden",
    "unexpected-special-method-signature",
    "inherit-non-class",
    "duplicate-except",
    "bad-except-order",
    "raising-bad-type",
    "raising-non-exception",
    "catching-non-exception",
    "bad-indentation",
    "E9996",
    "E9991",
    "E0001",
    "E9999",
    "unexpected-keyword-arg",
    "not-an-iterable",
    "nonexistent-operator",
    "invalid-length-returned",
    "abstract-method",
    "self-cls-assignment",
    "dict-iter-missing-items",
}
