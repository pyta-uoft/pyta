import os

import pylint.testutils
import pytest
from astroid import MANAGER

from python_ta.checkers.static_type_checker import StaticTypeChecker


class TestStaticTypeChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = StaticTypeChecker

    def test_e9951_incompatible_argument_type(self) -> None:
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/e9951_incompatible_argument_type.py",
            )
        )
        mod = MANAGER.ast_from_file(file_path)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="incompatible-argument-type",
                line=5,
                col_offset=23,
                end_line=5,
                end_col_offset=28,
                args=("1", "calculate_area", "str", "float"),
            ),
            pylint.testutils.MessageTest(
                msg_id="incompatible-argument-type",
                line=11,
                col_offset=27,
                end_line=11,
                end_col_offset=27,
                args=("1", "convert_to_upper", "int", "str"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_e9952_incompatible_assignment(self) -> None:
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/e9952_incompatible_assignment.py",
            )
        )
        mod = MANAGER.ast_from_file(file_path)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="incompatible-assignment",
                line=2,
                col_offset=7,
                end_line=2,
                end_col_offset=19,
                args=("str", "int"),
            ),
            pylint.testutils.MessageTest(
                msg_id="incompatible-assignment",
                line=4,
                col_offset=14,
                end_line=4,
                end_col_offset=18,
                args=("str", "int"),
            ),
        ):
            self.checker.process_module(mod)

    def test_e9953_list_item_type_mismatch(self) -> None:
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/e9953_list_item_type_mismatch.py",
            )
        )
        mod = MANAGER.ast_from_file(file_path)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="list-item-type-mismatch",
                line=1,
                col_offset=37,
                end_line=1,
                end_col_offset=37,
                args=("2", "int", "str"),
            ),
            pylint.testutils.MessageTest(
                msg_id="list-item-type-mismatch",
                line=3,
                col_offset=29,
                end_line=3,
                end_col_offset=35,
                args=("2", "str", "int"),
            ),
            pylint.testutils.MessageTest(
                msg_id="list-item-type-mismatch",
                line=5,
                col_offset=33,
                end_line=5,
                end_col_offset=37,
                args=("2", "str", "float"),
            ),
        ):
            self.checker.process_module(mod)

    def test_e9954_unsupported_operand_types(self) -> None:
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/e9954_unsupported_operand_types.py",
            )
        )
        mod = MANAGER.ast_from_file(file_path)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unsupported-operand-types",
                line=1,
                col_offset=10,
                end_line=1,
                end_col_offset=10,
                args=("-", "str", "int"),
            ),
            pylint.testutils.MessageTest(
                msg_id="unsupported-operand-types",
                line=3,
                col_offset=14,
                end_line=3,
                end_col_offset=17,
                args=("+", "int", "str"),
            ),
            pylint.testutils.MessageTest(
                msg_id="unsupported-operand-types",
                line=5,
                col_offset=15,
                end_line=5,
                end_col_offset=17,
                args=("*", "float", "str"),
            ),
        ):
            self.checker.process_module(mod)

    def test_e9955_union_attr_error(self) -> None:
        """Test for union attribute errors (E9955)."""
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/e9955_union_attr_error.py",
            )
        )
        mod = MANAGER.ast_from_file(file_path)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="union-attr-error",
                line=4,
                col_offset=13,  # Adjusted to match "Got"
                end_line=5,  # Adjusted to match "Got"
                end_col_offset=18,  # Adjusted to match "Got"
                args=("int", "upper"),
            ),
            pylint.testutils.MessageTest(
                msg_id="union-attr-error",
                line=4,
                col_offset=13,  # Adjusted to match "Got"
                end_line=5,  # Adjusted to match "Got"
                end_col_offset=18,  # Adjusted to match "Got"
                args=("float", "upper"),
            ),
            pylint.testutils.MessageTest(
                msg_id="union-attr-error",
                line=9,  # Adjusted to match "Got"
                col_offset=12,  # Matches "Got"
                end_line=9,  # Matches "Got"
                end_col_offset=20,  # Matches "Got"
                args=("list[Any]", "keys"),
            ),
        ):
            self.checker.process_module(mod)

    def test_e9956_dict_item_type_mismatch(self) -> None:
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/e9956_dict_item_type_mismatch.py",
            )
        )
        if not os.path.exists(file_path):
            raise FileNotFoundError(f"Test file not found: {file_path}")

        mod = MANAGER.ast_from_file(file_path)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="dict-item-type-mismatch",
                line=1,
                col_offset=45,
                end_line=1,
                end_col_offset=54,
                args=("2", "str", "int", "int", "str"),
            ),
            pylint.testutils.MessageTest(
                msg_id="dict-item-type-mismatch",
                line=3,
                col_offset=50,
                end_line=3,
                end_col_offset=60,
                args=("2", "int", "str", "str", "float"),
            ),
        ):
            self.checker.process_module(mod)

    def test_no_errors_in_static_type_checker_no_error(self) -> None:
        file_path = os.path.normpath(
            os.path.join(
                __file__,
                "../../../examples/custom_checkers/static_type_checker_examples/static_type_checker_no_error.py",
            )
        )
        mod = MANAGER.ast_from_file(file_path)
        with self.assertNoMessages():
            self.checker.process_module(mod)
