"""Monkeypatch pylint behaviour.
"""
from .checkers import patch_checkers


def patch_all():
    """Execute all patches defined in this module."""
    patch_checkers()
