"""checker for unnecessary indexing in a loop.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import List, Optional, Union
from astroid.node_classes import NodeNG


class UnnecessaryIndexingChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'unnecessary_indexing'
    # use dashes for connecting words in message symbol
    msgs = {'E9994': (f'Unnecessary loop variable "%s" in for loop',
                      'unnecessary-indexing',
                      'Used when you have an loop variable in a for loop '
                      'where its only usage is to index the iterable'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages("unnecessary-indexing")
    def visit_for(self, node: astroid.For) -> None:
        if self._is_unnecessary_indexing(node):
            args = f'{node.target.name}'
            self.add_message('unnecessary-indexing', node=node.target, args=args)

    def _is_unnecessary_indexing(self, node: astroid.For) -> bool:
        """Return whether the usage of the iteration variable in the for loop is ONLY to index the iterable.
        True if unnecessary usage, False otherwise or if iteration variable not used at all.
        """
        # Check if the iterable of the for loop is of the form "range(len(lst))".
        iterable = _iterable_if_range(node.iter)
        if iterable is None:
            return False

        index_nodes = _index_name_nodes(node.target.name, node)
        return all(_is_redundant(index_node, node) for index_node in index_nodes) and index_nodes


# Helper functions
def _iterable_if_range(node: Optional[NodeNG]) -> Optional[str]:
    """Return the iterable's name if this node is of the form: range(len(iterable)).
    Return None otherwise.
    """
    if (isinstance(node, astroid.Call) and
            isinstance(node.func, astroid.Name) and
            node.func.name == 'range' and
            isinstance(node.args[0], astroid.Call) and
            isinstance(node.args[0].func, astroid.Name) and
            node.args[0].func.name == 'len' and
            isinstance(node.args[0].args[0], astroid.Name)):
            return node.args[0].args[0].name


def _is_load_subscript(index_node: astroid.Name, for_node: astroid.For) -> bool:
    """Return whether or not <index_node> is used to subscript the iterable of <for_node>
    and the subscript item is being loaded from, e.g., s += iterable[index_node].
    """
    iterable = _iterable_if_range(for_node.iter)
    # Name node is not inside Subscript node iterable[index].
    if not (isinstance(index_node.parent, astroid.Index) and isinstance(index_node.parent.parent, astroid.Subscript)
            and index_node.parent.parent.value.name == iterable):
        return False
    # Use subscript.ctx attribute to find out what context it is being used in.
    subscript_node = index_node.parent.parent
    return subscript_node.ctx == astroid.Load


def _is_redundant(index_node: Union[astroid.AssignName, astroid.Name], for_node: astroid.For) -> bool:
    """Return whether or not <index_node> is redundant in <for_node>."""
    if isinstance(index_node, astroid.AssignName):
        return index_node.lookup(index_node.name)[1][0] != for_node.target or \
               not isinstance(index_node.parent, astroid.AugAssign)
    return index_node.lookup(index_node.name)[1][0] != for_node.target or _is_load_subscript(index_node, for_node)


def _index_name_nodes(index: str, for_node: astroid.For) -> List[Union[astroid.AssignName, astroid.Name]]:
    """Return a list of <index> AssignName and Name nodes contained in the body of <for_node>."""
    return [name_node for name_node in for_node.nodes_of_class((astroid.AssignName, astroid.Name))
            if name_node.name == index and name_node != for_node.target]


def register(linter):
    linter.register_checker(UnnecessaryIndexingChecker(linter))
