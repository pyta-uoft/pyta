"""checker for a while loop that does not mutate any condition variable in its body.
"""
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from typing import Set, Generator, Dict
from python_ta.cfg import CFGBlock


class PossibleInfiniteLoopChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'possible_infinite_loop'
    # use dashes for connecting words in message symbol
    msgs = {'E9976': ('This loop might not terminate.',
                      'possible-infinite-loop',
                      'Reported when the variable/s used in the while loop condition'
                      'is not mutated in any path of the code.'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages('possible-infinite-loop')
    def visit_while(self, node):
        """Adds a message if the variable used in the loop condition is not mutated in
        any path of the loop body.
        """
        # [var_name, True iff the inf_type is an immutable type].
        names: Dict[str, bool] = {}
        local_vars = self._get_local_vars(node)

        for n in node.test.nodes_of_class(astroid.Name, (astroid.Call, astroid.Attribute)):
            if n.name not in local_vars or not any(isinstance(o, astroid.AssignName) for o in local_vars[n.name]):
                continue

            val = n.inf_type.getValue()
            t = val.__name__ if type(val) is type else ''
            names[n.name] = t in ('str', 'int', 'float', 'bool', 'tuple', 'frozenset')

        if len(names) < 1:
            return

        for n in node.nodes_of_class((astroid.AssignName, astroid.Name), (astroid.FunctionDef)):
            if n is node.test or n.parent is node.test or isinstance(n.parent, astroid.Call) and n is n.parent.func:
                continue
            if n.name in names and (isinstance(n, astroid.Name) and not names[n.name]\
                    or isinstance(n, astroid.AssignName)):
                    return

        self.add_message('possible-infinite-loop', node=node)

    def _get_local_vars(self, node: astroid.While):
        """Returns the local variables in the enclosing scope."""
        v = node.scope().locals
        for n in node.scope().nodes_of_class(astroid.Nonlocal, astroid.FunctionDef):
            if isinstance(n, astroid.Nonlocal):
                # nonlocal declaration must happen before usage
                for name in n.names:
                    try:
                        del v[name]
                    except KeyError:
                        pass
        return v


def register(linter):
    linter.register_checker(PossibleInfiniteLoopChecker(linter))
