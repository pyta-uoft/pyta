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
            if not (name in node.frame() or name in node.root()):
                if name == 'range':
                    # the arguments of 'range' call
                    arg = node.args
                    flag = True
                    # check if there is no args in 'range' call
                    if len(arg) == 0:
                        flag = False
                    # check if all the args are integer
                    if not all([isinstance(literal_eval(c.as_string()), int) for c in arg]):
                        flag = False
                    # check the stop index
                    if len(arg) == 1:
                        if literal_eval(arg[0].as_string()) < 2:
                            flag = False
                    # check the stop index
                    if len(arg) == 2:
                        if literal_eval(arg[1].as_string()) < 2:
                            flag = False
                    if len(arg) == 3:
                        a = literal_eval(arg[0].as_string())
                        b = literal_eval(arg[1].as_string())
                        c = literal_eval(arg[2].as_string())
                        if abs(c) >= abs(a - b):
                             flag = False
                        # check if the step index is zero
                        if c == 0:
                            flag = False
                        # check if the step index has effect
                        if a > b and c < 0:
                            flag = False

                        if a < b and c > 0:
                            flag = False
                    if not flag:
                        args = "{}".format(node.lineno)
                        self.add_message('invalid-range-index', node=node,
                                     args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(InvalidRangeIndexChecker(linter))
