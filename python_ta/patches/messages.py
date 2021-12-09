"""Patch pylint message-handling behaviour."""
from pylint.interfaces import UNDEFINED
from pylint.lint import PyLinter


def patch_messages():
    """Patch PyLinter to pass the node to reporter."""
    old_add_message = PyLinter.add_message

    def new_add_message(
        self,
        msg_id,
        line=None,
        node=None,
        args=None,
        confidence=UNDEFINED,
        col_offset=None,
        end_lineno=None,
        end_col_offset=None,
    ):
        old_add_message(
            self, msg_id, line, node, args, confidence, col_offset, end_lineno, end_col_offset
        )
        msg_info = self.msgs_store.get_message_definitions(msg_id)[0]
        # guard to allow for backward compatability with Pylint's reporters
        if hasattr(self.reporter, "handle_node"):
            self.reporter.handle_node(msg_info, node)

    PyLinter.add_message = new_add_message
