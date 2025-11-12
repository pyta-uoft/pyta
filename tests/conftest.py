import re
from http.server import HTTPServer

import pytest

import python_ta.contracts

Z3_RELATED_TESTS = {
    r".*test_z3_constraints.*",
    r".*test_edge_feasibility.*",
    r".*test_impossible_condition_checker.*",
    r".*test_redundant_condition_checker.*",
    r".*test_z3_parser.*",
    r".*test_z3_visitor.*",
    r".*test_inconsistent_returns.*",
    r".*test_missing_return_statements.*",
    r".*test_one_iteration_checker.*",
    r".*test_possibly_undefined_checker.*",
    r".*test_redundant_assignment_checker.*",
    r".*test_cfg_generator_z3.*",
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


def pytest_ignore_collect(path, config):
    """Return True to prevent collecting a test file or directory.
    Note: this function must return None for test cases not intended to exclude. Otherwise, it will interfere
    with other configurations such as --exclude flag.

    Refer to the following docstring in Pytest source code:

    Return ``True`` to ignore this path for collection.

    Return ``None`` to let other plugins ignore the path for collection.

    Returning ``False`` will forcefully *not* ignore this path for collection,
    without giving a chance for other plugins to ignore this path.
    https://github.com/pytest-dev/pytest/blob/main/src/_pytest/hookspec.py
    """
    if config.getoption("--exclude-z3"):
        # Convert path to string for pattern matching
        path_str = str(path)
        if any(re.search(pattern, path_str) for pattern in Z3_RELATED_TESTS):
            return True
        else:
            return None

    return None
