from typing import List

import pylint.testutils
import astroid
from python_ta.checkers.invalid_for_target_checker import InvalidForTargetChecker


class TestInvalidForTargetChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidForTargetChecker

    def _assert_no_message(self, src: str) -> None:
        for_node, *_ = _extract_nodes(src, [astroid.For])

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
        for_node, subscript_node = _extract_nodes(src, [astroid.For, astroid.Subscript])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=subscript_node,
                    args='l[0]'
                )
        ):
            self.checker.visit_for(for_node)

    def test_message_simple_assign_attr(self) -> None:
        """Test that a message is added when a for target assigns to an attribute"""
        src = """
        for x.attr in l:
            pass
        """
        for_node, assign_attr_node = _extract_nodes(src, [astroid.For, astroid.AssignAttr])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=assign_attr_node,
                    args='x.attr'
                )
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
        for_node, subscript_node = _extract_nodes(src, [astroid.For, astroid.Subscript])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=subscript_node,
                    args='b[0]'
                )
        ):
            self.checker.visit_for(for_node)

    def test_no_msg_list_simple(self) -> None:
        """Test that no message is added when the for target list only contains valid targets
        """
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
        for_node, subscript_node = _extract_nodes(src, [astroid.For, astroid.Subscript])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=subscript_node,
                    args='b[0]'
                )
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
        for_node, subscript_node = _extract_nodes(src, [astroid.For, astroid.Subscript])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=subscript_node,
                    args='d[0]'
                )
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
        for_node, subscript_node = _extract_nodes(src, [astroid.For, astroid.Subscript])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=subscript_node,
                    args='d[0]'
                )
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
        for_node, subscript_node = _extract_nodes(src, [astroid.For, astroid.Subscript])

        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='invalid-for-target',
                    node=subscript_node,
                    args='d[0]'
                )
        ):
            self.checker.visit_for(for_node)


def _extract_nodes(src: str, node_types: List[type]) -> List[astroid.node_classes.NodeNG]:
    mod = astroid.parse(src)

    extracted_nodes = []
    for node_type in node_types:
        node, *_ = mod.nodes_of_class(node_type)
        extracted_nodes.append(node)

    return extracted_nodes
