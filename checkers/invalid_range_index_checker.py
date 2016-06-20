import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from ast import literal_eval


class InvalidRangeIndexChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'custom'
    msgs = {'E9993':
                ('You should not use invalid range index on line %s',
                 'invalid-range-index',
                 'Used when you use invalid index range')}
    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("invalid-range-index")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()) and name == 'range':
                # the arguments of 'range' call
                arg = node.args
                # check if there is no args in 'range' call
                if len(arg) == 0 or \
                        not all([isinstance(literal_eval(c.as_string()), int) for c in arg])\
                    or (len(arg) == 1 and literal_eval(arg[0].as_string()) < 2)\
                    or (len(arg) == 2 and literal_eval(arg[1].as_string()) < 2):
                    args = "{}".format(node.lineno)
                    self.add_message('invalid-range-index', node=node,
                                 args=args)
                if len(arg) == 3:
                    a = literal_eval(arg[0].as_string())
                    b = literal_eval(arg[1].as_string())
                    c = literal_eval(arg[2].as_string())
                    if abs(c) >= abs(a - b) or c == 0 or (a > b and c < 0) or \
                                            a < b and c > 0:
                        args = "{}".format(node.lineno)
                        self.add_message('invalid-range-index', node=node,
                                 args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(InvalidRangeIndexChecker(linter))
