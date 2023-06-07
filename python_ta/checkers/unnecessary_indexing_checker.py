"""checker for unnecessary indexing in a loop.
"""
from typing import List, Optional, Tuple, Union

import astroid
from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages


class UnnecessaryIndexingChecker(BaseChecker):
    # name is the same as file name but without _checker part
    name = "unnecessary_indexing"
    # use dashes for connecting words in message symbol
    msgs = {
        "E9994": (
            "Loop/comprehension index `%s` can be simplified by accessing the elements directly in the for loop or "
            "comprehension, "
            "for example, `for my_variable in %s`.",
            "unnecessary-indexing",
            "Used when you have an index variable in a for loop/comprehension "
            "where its only usage is to index the iterable",
        )
    }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of only_required_for_messages
    @only_required_for_messages("unnecessary-indexing")
    def visit_for(self, node: nodes.For) -> None:
        # Check if the iterable of the for loop is of the form "range(len(<variable-name>))".
        iterable = _iterable_if_range(node.iter)
        if iterable is not None and _is_unnecessary_indexing(node):
            args = node.target.as_string(), iterable
            self.add_message("unnecessary-indexing", node=node.target, args=args)

    @only_required_for_messages("unnecessary-indexing")
    def visit_comprehension(self, node: nodes.Comprehension) -> None:
        iterable = _iterable_if_range(node.iter)
        if iterable is not None and _is_unnecessary_indexing(node):
            args = node.target.as_string(), iterable
            self.add_message("unnecessary-indexing", node=node.target, args=args)


# Helper functions
def _is_unnecessary_indexing(node: Union[nodes.For, nodes.Comprehension]) -> bool:
    """Return whether the index variable in the for loop/comprehension is ONLY used to index the iterable.

    True if unnecessary usage, False otherwise or if index variable not used at all.
    """
    index_nodes = []
    for assign_name_node in node.target.nodes_of_class((nodes.AssignName, nodes.Name)):
        index_nodes.extend(_index_name_nodes(assign_name_node.name, node))
    return all(_is_redundant(index_node, node) for index_node in index_nodes) and index_nodes


def _iterable_if_range(node: nodes.NodeNG) -> Optional[str]:
    """Return the iterable's name if this node is in "range" form, or None otherwise.

    Check for three forms:
      - range(len(<variable-name>))
      - range(0, len(<variable-name>))
      - range(0, len(<variable-name>), 1)
    """
    # Check outer function call is range
    if (
        not isinstance(node, nodes.Call)
        or not isinstance(node.func, nodes.Name)
        or not node.func.name == "range"
    ):
        return None

    # Check arguments to range
    if len(node.args) > 1:
        # Check that args[0] == Const(0)
        arg1 = node.args[0]
        if not isinstance(arg1, nodes.Const) or arg1.value != 0:
            return None
        if len(node.args) == 3 and (
            not isinstance(node.args[2], nodes.Const) or node.args[2].value != 1
        ):
            return None

    # Finally, check 'stop' argument is of the form len(<variable-name>).
    if len(node.args) == 1:
        stop_arg = node.args[0]
    else:
        stop_arg = node.args[1]

    if (
        isinstance(stop_arg, nodes.Call)
        and isinstance(stop_arg.func, nodes.Name)
        and stop_arg.func.name == "len"
        and len(stop_arg.args) == 1
        and isinstance(stop_arg.args[0], nodes.Name)
    ):
        return stop_arg.args[0].name


def _is_load_subscript(
    index_node: nodes.Name, loop_node: Union[nodes.For, nodes.Comprehension]
) -> bool:
    """Return whether or not <index_node> is used to subscript the iterable of <loop_node>
    and the subscript item is being loaded from, e.g., s += iterable[index_node].

    NOTE: Index node is deprecated in Python 3.9

    Returns True if the following conditions are met:
    (3.9)
        - The <index_node> Name node is inside of a Subscript node
        - The item that is being indexed is the iterable of the for loop/comprehension
        - The Subscript node is being used in a load context
    (3.8)
        - The <index_node> Name node is inside of an Index node
        - The Index node is inside of a Subscript node
        - The item that is being indexed is the iterable of the for loop/comprehension
        - The Subscript node is being used in a load context
    """
    iterable = _iterable_if_range(loop_node.iter)

    return (
        isinstance(index_node.parent, nodes.Subscript)
        and isinstance(index_node.parent.value, nodes.Name)
        and index_node.parent.value.name == iterable
        and index_node.parent.ctx == astroid.Load
    )


def _is_redundant(
    index_node: Union[nodes.AssignName, nodes.Name],
    loop_node: Union[nodes.For, nodes.Comprehension],
) -> bool:
    """Return whether or not <index_node> is redundant in <loop_node>.

    The lookup method is used in case the original index variable is shadowed
    in the for loop/comprehension's body.
    """
    _, assignments = index_node.lookup(index_node.name)
    if not assignments:
        return False
    elif isinstance(index_node, nodes.AssignName):
        return assignments[0] != loop_node.target
    else:  # isinstance(index_node, nodes.Name)
        return assignments[0] != loop_node.target or _is_load_subscript(index_node, loop_node)


def _index_name_nodes(
    index: str, loop_node: Union[nodes.For, nodes.Comprehension]
) -> List[Union[nodes.AssignName, nodes.Name]]:
    """Return a list of <index> AssignName and Name nodes contained in the body of <loop_node>.

    Remove uses of variables that shadow <index>.
    """
    scope = loop_node.scope()

    if isinstance(loop_node, nodes.For):
        body = loop_node
    else:
        body = loop_node.parent

    return [
        name_node
        for name_node in body.nodes_of_class((nodes.AssignName, nodes.Name))
        if name_node.name == index
        and name_node != loop_node.target
        and name_node.lookup(name_node.name)[0] == scope
    ]


def register(linter):
    linter.register_checker(UnnecessaryIndexingChecker(linter))
