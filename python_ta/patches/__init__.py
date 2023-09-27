"""Monkeypatch pylint behaviour.
"""
from .checkers import patch_checkers
from .error_messages import patch_error_messages
from .messages import patch_messages
from .transforms import patch_ast_transforms


def patch_all(messages_config: dict, overwrite_error_messages: bool):
    """Execute all patches defined in this module."""
    patch_checkers()
    patch_ast_transforms()
    patch_messages()
    if overwrite_error_messages:
        patch_error_messages(messages_config)
