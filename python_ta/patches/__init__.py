"""Monkeypatch pylint behaviour.
"""
from .checkers import patch_checkers
from .error_messages import patch_error_messages
from .messages import patch_linter_transform, patch_messages
from .transforms import patch_ast_transforms


def patch_all():
    """Execute all patches defined in this module."""
    patch_checkers()
    patch_ast_transforms()
    patch_messages()
    patch_linter_transform()
    patch_error_messages()
