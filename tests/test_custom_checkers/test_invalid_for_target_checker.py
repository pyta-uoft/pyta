from __future__ import annotations

import astroid
import pylint.testutils
from astroid import nodes

from python_ta.checkers.invalid_for_target_checker import InvalidForTargetChecker


class TestInvalidForTargetChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidForTargetChecker

    def _assert_no_message(self, src: str) -> None:
        for_node, *_ = _extract_nodes(src, [nodes.For])

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_no_message_simple(self) -> None:
        """Test that no message is added when a for target is an assign name"""
        src = """
        for i in l:
            pass
        """
        self._assert_no_message(src)

    def test_message_simple_subscript(self) -> None:
        """Test that a message is added when a for target is a subscript"""
        src = """
        for l[0] in l:
            pass
        """
        for_node, subscript_node = _extract_nodes(src, [nodes.For, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="l[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_message_simple_assign_attr(self) -> None:
        """Test that a message is added when a for target assigns to an attribute"""
        src = """
        for x.attr in l:
            pass
        """
        for_node, assign_attr_node = _extract_nodes(src, [nodes.For, nodes.AssignAttr])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=assign_attr_node, args="x.attr"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_tuple_simple(self) -> None:
        """Test that no message is added when the for target tuple only contains valid targets
        Note: a target with commas but no parentheses becomes a Tuple node.
        """
        src = """
        for a, b in l:
            pass
        """
        self._assert_no_message(src)

    def test_msg_tuple_simple(self) -> None:
        """Test that a message is added when a for target tuple contains invalid targets"""
        src = """
        for a, b[0] in l:
            pass
        """
        for_node, subscript_node = _extract_nodes(src, [nodes.For, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="b[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_list_simple(self) -> None:
        """Test that no message is added when the for target list only contains valid targets"""
        src = """
        for [a, b] in l:
            pass
        """
        self._assert_no_message(src)

    def test_msg_list_simple(self) -> None:
        """Test that a message is added when a for target list contains invalid targets"""
        src = """
        for [a, b[0]] in l:
            pass
        """
        for_node, subscript_node = _extract_nodes(src, [nodes.For, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="b[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_tuple_nested(self) -> None:
        """Test that no message is added when for target nested tuples only contain valid targets"""
        src = """
        for a, (b, (c, d), e) in l:
            pass
        """
        self._assert_no_message(src)

    def test_msg_tuple_nested(self) -> None:
        """Test that a message is added when for target nested tuples contains invalid targets"""
        src = """
        for a, (b, (c, d[0]), e) in l:
            pass
        """
        for_node, subscript_node = _extract_nodes(src, [nodes.For, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="d[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_list_nested(self) -> None:
        """Test that no message is added when for target nested lists only contain valid targets"""
        src = """
        for [a, [b, [c, d], e]] in l:
            pass
        """
        self._assert_no_message(src)

    def test_msg_list_nested(self) -> None:
        """Test that a message is added when for target nested lists contains invalid targets"""
        src = """
        for [a, [b, [c, d[0]], e]] in l:
            pass
        """
        for_node, subscript_node = _extract_nodes(src, [nodes.For, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="d[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_tuple_and_list_nested(self) -> None:
        """Test that no message is added when for target nested tuples and lists
        only contain valid targets"""
        src = """
        for a, [b, (c, d), e] in l:
            pass
        """
        self._assert_no_message(src)

    def test_msg_tuple_and_list_nested(self) -> None:
        """Test that a message is added when for target nested tuples and lists
        contains invalid targets"""
        src = """
        for a, [b, (c, d[0]), e] in l:
            pass
        """
        for_node, subscript_node = _extract_nodes(src, [nodes.For, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="d[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_comp_simple(self) -> None:
        """Test that no message is added when the comprehension contains a valid target."""
        src = """
        [x for x in lst]
        """
        comp_node, *_ = _extract_nodes(src, [nodes.Comprehension])

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_subscript(self) -> None:
        """Test that a message is added when the comprehension contains an invalid target."""
        src = """
        [x for x[0] in x]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="x[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_assign_attr(self) -> None:
        """Test that a message is added when a comprehension target assigns to an attribute"""
        src = """
        [x for x.attr in l]
        """
        comp_node, assign_attr_node = _extract_nodes(src, [nodes.Comprehension, nodes.AssignAttr])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=assign_attr_node, args="x.attr"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_no_msg_comp_tuple_simple(self) -> None:
        """Test that no message is added when the comprehension target tuple only contains valid targets
        Note: a target with commas but no parentheses becomes a Tuple node.
        """
        src = """
        [a for a ,b in l]
        """
        comp_node, *_ = _extract_nodes(src, [nodes.Comprehension])

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_tuple_simple(self) -> None:
        """Test that a message is added when a comprehension target tuple contains invalid targets"""
        src = """
        [a for a, b[0] in l]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="b[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_no_msg_comp_list(self) -> None:
        """Test that no message is added when the comprehension target list only contains valid targets"""
        src = """
        [a for [a, b] in l]
        """
        comp_node, *_ = _extract_nodes(src, [nodes.Comprehension])

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_list(self) -> None:
        """Test that a message is added when a comprehension target list contains invalid targets"""
        src = """
        [a for [a, b[0]] in l]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="b[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_no_msg_comp_tuple_nested(self) -> None:
        """Test that no message is added when comprehension target nested tuples only contain valid targets"""
        src = """
        [a for a, (b, (c, d), e) in l]
        """
        comp_node, *_ = _extract_nodes(src, [nodes.Comprehension])

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_tuple_nested(self) -> None:
        """Test that a message is added when comprehension target nested tuples contains invalid targets"""
        src = """
        [a for a, (b, (c, d[0]), e) in l]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="d[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_no_msg_comp_list_nested(self) -> None:
        """Test that no message is added when comprehension target nested lists only contain valid targets"""
        src = """
        [a for [a, [b, [c, d], e]] in l]
        """
        comp_node, *_ = _extract_nodes(src, [nodes.Comprehension])

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_list_nested(self) -> None:
        """Test that a message is added when comprehension target nested lists contains invalid targets"""
        src = """
        [a for [a, [b, [c, d[0]], e]] in l]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="d[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_no_msg_comp_tuple_and_list_nested(self) -> None:
        """Test that no message is added when comprehension target nested tuples and lists
        only contain valid targets"""
        src = """
        [a for a, [b, (c, d), e] in l]
        """
        comp_node, *_ = _extract_nodes(src, [nodes.Comprehension])

        with self.assertNoMessages():
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_tuple_and_list_nested(self) -> None:
        """Test that a message is added when comprehension target nested tuples and lists
        contains invalid targets"""
        src = """
        [a for a, [b, (c, d[0]), e] in l]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="d[0]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)

    def test_msg_comp_slicing(self) -> None:
        """Test that a message is added when the comprehension target is a list slice"""
        src = """
        [a for a[1:] in l]
        """
        comp_node, subscript_node = _extract_nodes(src, [nodes.Comprehension, nodes.Subscript])

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-for-target", node=subscript_node, args="a[1:]"
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comp_node)


def _extract_nodes(src: str, node_types: list[type]) -> list[nodes.NodeNG]:
    mod = astroid.parse(src)

    extracted_nodes = []
    for node_type in node_types:
        node, *_ = mod.nodes_of_class(node_type)
        extracted_nodes.append(node)

    return extracted_nodes
