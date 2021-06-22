"""checker for unnecessary indexing in a loop.
"""
from typing import List, Optional, Tuple, Union

import sys
import astroid
from astroid.node_classes import NodeNG
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from pylint.interfaces import IAstroidChecker


class UnnecessaryIndexingChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'unnecessary_indexing'
    # use dashes for connecting words in message symbol
    msgs = {'E9994': ('For loop variable "%s" can be simplified',
                      'unnecessary-indexing',
                      'Used when you have an loop variable in a for loop '
                      'where its only usage is to index the iterable'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages('unnecessary-indexing')
    def visit_for(self, node: astroid.For) -> None:
        if _is_unnecessary_indexing(node):
            args = node.target.name
            self.add_message('unnecessary-indexing', node=node.target, args=args)


# Helper functions
def _is_unnecessary_indexing(node: astroid.For) -> bool:
    """Return whether the iteration variable in the for loop is ONLY used to index the iterable.

    True if unnecessary usage, False otherwise or if iteration variable not used at all.
    """
    # Check if the iterable of the for loop is of the form "range(len(<variable-name>))".
    iterable = _iterable_if_range(node.iter)
    if iterable is None:
        return False

    index_nodes = _index_name_nodes(node.target.name, node)
    return all(_is_redundant(index_node, node) for index_node in index_nodes) and index_nodes


def _iterable_if_range(node: NodeNG) -> Optional[str]:
    """Return the iterable's name if this node is in "range" form, or None otherwise.

    Check for three forms:
      - range(len(<variable-name>))
      - range(0, len(<variable-name>))
      - range(0, len(<variable-name>), 1)
    """
    # Check outer function call is range
    if (not isinstance(node, astroid.Call) or
            not isinstance(node.func, astroid.Name) or
            not node.func.name == 'range'):
        return None

    # Check arguments to range
    if len(node.args) > 1:
        # Check that args[0] == Const(0)
        arg1 = node.args[0]
        if not isinstance(arg1, astroid.Const) or arg1.value != 0:
            return None
        if len(node.args) == 3 and (
                not isinstance(node.args[2], astroid.Const) or node.args[2].value != 1):
            return None

    # Finally, check 'stop' argument is of the form len(<variable-name>).
    if len(node.args) == 1:
        stop_arg = node.args[0]
    else:
        stop_arg = node.args[1]

    if (isinstance(stop_arg, astroid.Call) and
            isinstance(stop_arg.func, astroid.Name) and
            stop_arg.func.name == 'len' and
            len(stop_arg.args) == 1 and
            isinstance(stop_arg.args[0], astroid.Name)):
        return stop_arg.args[0].name


def _is_load_subscript(index_node: astroid.Name, for_node: astroid.For) -> bool:
    """Return whether or not <index_node> is used to subscript the iterable of <for_node>
    and the subscript item is being loaded from, e.g., s += iterable[index_node].

    NOTE: Index node is deprecated in Python 3.9

    Returns True if the following conditions are met:
    (3.9)
        - The <index_node> Name node is inside of a Subscript node
        - The item that is being indexed is the iterable of the for loop
        - The Subscript node is being used in a load context
    (3.8)
        - The <index_node> Name node is inside of an Index node
        - The Index node is inside of a Subscript node
        - The item that is being indexed is the iterable of the for loop
        - The Subscript node is being used in a load context
    """
    iterable = _iterable_if_range(for_node.iter)

    if sys.version_info >= (3, 9):
        return (
                isinstance(index_node.parent, astroid.Subscript) and
                isinstance(index_node.parent.value, astroid.Name) and
                index_node.parent.value.name == iterable and
                index_node.parent.ctx == astroid.Load
        )
    else:
        return (
                isinstance(index_node.parent, astroid.Index) and
                isinstance(index_node.parent.parent, astroid.Subscript) and
                isinstance(index_node.parent.parent.value, astroid.Name) and
                index_node.parent.parent.value.name == iterable and
                index_node.parent.parent.ctx == astroid.Load
        )


def _is_redundant(index_node: Union[astroid.AssignName, astroid.Name], for_node: astroid.For) -> bool:
    """Return whether or not <index_node> is redundant in <for_node>.

    The lookup method is used in case the original loop variable is shadowed
    in the for loop's body.
    """
    if isinstance(index_node, astroid.AssignName):
        previous_context = index_node.lookup(index_node.name)
        if previous_context[1] != ():
            return (
                    previous_context[1][0] != for_node.target
                    and previous_context[0] is for_node.scope()
            )
        else:
            return False
    else:
        return _scope_lookup(index_node) != for_node.target or _is_load_subscript(index_node, for_node)


def _index_name_nodes(index: str, for_node: astroid.For) -> List[Union[astroid.AssignName, astroid.Name]]:
    """Return a list of <index> AssignName and Name nodes contained in the body of <for_node>."""
    return [name_node for name_node in for_node.nodes_of_class((astroid.AssignName, astroid.Name))
            if name_node.name == index and name_node != for_node.target]


def _scope_lookup(node: astroid.Name) -> Optional[NodeNG]:
    """Look up the given name node's assigment node.

    This is a replacement for astroid's LocalsDictNodeNG._scope_lookup method, which doesn't
    seem to handle nested comprehensions (?).
    """
    scope = node.scope()
    while node.name not in scope and not isinstance(scope, astroid.Module):
        scope = scope.parent.scope()

    if node.name in scope:
        return scope[node.name]
    else:
        return None


def register(linter):
    linter.register_checker(UnnecessaryIndexingChecker(linter))
