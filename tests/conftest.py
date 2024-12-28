import re
from http.server import HTTPServer

import pytest

import python_ta.contracts

Z3_RELATED_TESTS = {
    r"tests/test_z3_constraints\.py",
    r"tests/test_edge_feasibility\.py",
    r"tests/test_impossible_condition_checker\.py",
    r"tests/test_redundant_condition_checker\.py",
    r"tests/test_z3_parser\.py",
    r".*TestInconsistentReturnCheckerZ3Option.*",
    r".*TestMissingReturnCheckerZ3Option.*",
    r".*TestOneIterationCheckerZ3Option.*",
    r".*TestPossiblyUndefinedCheckerZ3Option.*",
    r".*TestRedundantAssignmentCheckerZ3Option.*",
}


@pytest.fixture()
def disable_contract_checking():
    """Fixture for setting python_ta.contracts.ENABLE_CONTRACT_CHECKING = False."""
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = False
    yield
    python_ta.contracts.ENABLE_CONTRACT_CHECKING = True


@pytest.fixture()
def disable_strict_numeric_types():
    """Fixture for setting python_ta.contracts.STRICT_NUMERIC_TYPES = False."""
    python_ta.contracts.STRICT_NUMERIC_TYPES = False
    yield
    python_ta.contracts.STRICT_NUMERIC_TYPES = True


@pytest.fixture()
def prevent_webbrowser_and_httpserver(mocker):
    """Automatically mock webbrowser.open and HTTPServer.handle_request in all tests. this prevents any browser/server
    code running when running Pytest to avoid CI timeouts, and unexpected browser popups."""
    mocker.patch("webbrowser.open", return_value=None)
    mocker.patch.object(HTTPServer, "handle_request", return_value=None)


def pytest_addoption(parser):
    """Custom command-line options to enable/disable exclusion of certain tests"""
    parser.addoption(
        "--exclude-z3",
        action="store_true",
        default=False,
        help="Exclude test cases the require z3 dependency.",
    )


def pytest_collection_modifyitems(config, items):
    """Modify collected test items to exclude certain tests based on configuration."""
    if config.getoption("--exclude-z3"):
        skip_z3 = pytest.mark.skip(reason="Test requires z3-solver")
        for item in items:
            if any(re.search(pattern, item.nodeid) for pattern in Z3_RELATED_TESTS):
                item.add_marker(skip_z3)
