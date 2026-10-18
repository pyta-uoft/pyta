"""Tests for PythonTA documentation URL generation."""

import pytest

from python_ta.util.documentation import get_documentation_url


@pytest.mark.parametrize(
    "msg_id, expected_url",
    [
        ("E0401", "https://www.cs.toronto.edu/~david/pyta/checkers/index.html#e0401"),
        ("e0401", "https://www.cs.toronto.edu/~david/pyta/checkers/index.html#e0401"),
        ("E9992", "https://www.cs.toronto.edu/~david/pyta/checkers/index.html#e9992"),
        ("C0114", "https://www.cs.toronto.edu/~david/pyta/checkers/index.html#c0114"),
    ],
    ids=["uppercase", "lowercase", "custom-checker", "undocumented-check"],
)
def test_get_documentation_url(msg_id: str, expected_url: str) -> None:
    """Tests that the expected documentation URLs are returned."""
    assert get_documentation_url(msg_id) == expected_url
