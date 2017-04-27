"""Monkeypatch pylint behaviour.
"""
from .checkers import patch_checkers
from .type import patch_type_inference_transform


def patch_all():
    """Execute all patches defined in this module."""
    patch_checkers()
    patch_type_inference_transform()
