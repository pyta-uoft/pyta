from http.server import HTTPServer

import pytest

import python_ta.contracts

Z3_RELATED_TESTS = [
    "test_z3_constraints.py",
    "test_edge_feasibility.py",
    "test_custom_checkers/test_impossible_condition_checker.py",
    "test_custom_checkers/test_redundant_condition_checker.py",
    "test_custom_checkers/test_inconsistent_returns.py::TestInconsistentReturnCheckerZ3Option",
    "test_custom_checkers/test_missing_return_statements.py::TestMissingReturnCheckerZ3Option",
    "test_custom_checkers/test_one_iteration_checker.py::TestOneIterationCheckerZ3Option",
    "test_custom_checkers/test_possibly_undefined_checker.py::TestPossiblyUndefinedCheckerZ3Option",
    "test_custom_checkers/test_redundant_assignment_checker.py::TestRedundantAssignmentCheckerZ3Option",
    "test_z3/test_z3_parser.py",
    "test_z3_visitor.py",
]


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
    excluded_tests = []

    if config.getoption("--exclude-z3"):
        excluded_tests.extend(Z3_RELATED_TESTS)

    # filter out excluded tests
    items[:] = [item for item in items if item.nodeid not in excluded_tests]
