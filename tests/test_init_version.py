"""Test for __init__.py system version check"""
import sys
import importlib
import python_ta


def test_sys_version_log(caplog, monkeypatch) -> None:
    """Testing if message logged when system version is too low is correct"""
    monkeypatch.setattr(sys, "version_info", (2, 6, 0))
    importlib.reload(python_ta)  # Necessary due to python's import not actually reimporting package

    assert caplog.records[0].levelname == "WARNING"
    assert "You need Python 3.7 or later to run PythonTA." in caplog.text
