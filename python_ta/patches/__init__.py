"""Monkeypatch pylint behaviour.
"""
from .checkers import patch_checkers
from .messages import patch_messages, patch_linter_transform


def patch_all():
    """Execute all patches defined in this module."""
    patch_checkers()
    patch_messages()
    patch_linter_transform()
