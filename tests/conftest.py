import webbrowser
from http.server import HTTPServer
from unittest.mock import Mock

import pytest

import python_ta.contracts


@pytest.fixture()
def disable_contract_checking():
    """Fixture for setting python_ta.contracts.ENABLE_CONTRACT_CHECKING = False."""
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = False
    yield
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = True


@pytest.fixture()
def prevent_webbrowser_and_httpserver():
    """Automatically mock webbrowser.open and HTTPServer.handle_request in all tests. this prevents any owser/server
    code running when running Pytest to avoid CI timeouts, and unexpected browser popups."""
    original_webbrowser_open, original_httpserver_handle_request = (
        webbrowser.open,
        HTTPServer.handle_request,
    )
    webbrowser.open = Mock(return_value=None)
    HTTPServer.handle_request = Mock(return_value=None)
    yield
    webbrowser.open, HTTPServer.handle_request = (
        original_webbrowser_open,
        original_httpserver_handle_request,
    )
