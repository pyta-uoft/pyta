from http.server import HTTPServer

import pytest

import python_ta.contracts


@pytest.fixture()
def disable_contract_checking():
    """Fixture for setting python_ta.contracts.ENABLE_CONTRACT_CHECKING = False."""
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = False
    yield
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = True


@pytest.fixture()
def prevent_webbrowser_and_httpserver(mocker):
    """Automatically mock webbrowser.open and HTTPServer.handle_request in all tests. this prevents any browser/server
    code running when running Pytest to avoid CI timeouts, and unexpected browser popups."""
    mocker.patch("webbrowser.open", return_value=None)
    mocker.patch.object(HTTPServer, "handle_request", return_value=None)
