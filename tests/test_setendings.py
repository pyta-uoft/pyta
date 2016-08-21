"""
Tests for setendings.py, check `end_lineno` and `end_col_offset` 
properties are set.

Astroid Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py

See class and method docstrings for explanations.

Run: python tests/test_setendings.py
"""

from astroid.bases import NodeNG
# import astroid
import unittest
import logging
from setendings import *

# Set the log level (DEBUG, ERROR, ...), and message format.
logging.basicConfig(format='', level=logging.DEBUG)


class NodeNG(object):
    """Check `end_col_offset` and `end_lineno` properties are correctly set on
    the nodes. Use the node method `nodes_of_class`.
    https://github.com/PyCQA/astroid/blob/master/astroid/node_classes.py#L407
    """

    def __init__(self):
        super().__init__()
        self.reset()

    def reset(self):
        """Reset between test methods (and once on init).
        """
        # Keep a list rather than a set, because "too many" is wrong.
        self._props_check = []

    def check_endings(self, module, node_class):
        """Look at the nodes of a certain class, and inspect certain properties.
        """
        for node in module.nodes_of_class(node_class):  # generator
            try:
                self._props_check.append((node.fromlineno, node.end_lineno, 
                                        node.col_offset, node.end_col_offset))
            except AttributeError:
                # raise again to also get traceback along with message.
                raise AttributeError('''Make sure the properties are set in 
                    setendings.py and the function is registered
                    with ending_transformer.register_transform()''')
        return self._props_check


class TestEndingLocation(unittest.TestCase):
    """The method, ending_transformer.visit(module) walks the given astroid
    *tree* and transform each encountered node. Only the nodes which have
    transforms registered will actually be replaced or changed.
    
    We store the correct values as a tuple:
    (fromlineno, end_lineno, col_offset, end_col_offset)
    """

    @classmethod
    def setUpClass(self):
        """A class method called before tests in an individual class run.
        setUpClass is called with the class as the only argument and must be
        decorated as a classmethod():"""
        # Instantiate a visitor, and register the transform functions to it.
        self.ending_transformer = init_register_ending_setters()
        # Check the nodes property correctness.
        self.nodeng = NodeNG()

    def setUp(self):
        """Method called to prepare the test fixture. This is called immediately
        before calling the test method; other than AssertionError or SkipTest,
        any exception raised by this method will be considered an error rather
        than a test failure. The default implementation does nothing."""
        pass

    def tearDown(self):
        """Method called immediately after the test method has been called and
        the result recorded. This is called even if the test method raised an
        exception, so the implementation in subclasses may need to be
        particularly careful about checking internal state. Any exception,
        other than AssertionError or SkipTest, raised by this method will be
        considered an additional error rather than a test failure (thus
        increasing the total number of reported errors). This method will only
        be called if the setUp() succeeds, regardless of the outcome of the
        test method. The default implementation does nothing."""
        self.nodeng.reset()

    def get_file_as_module(self, file_location):
        """Given a filepath (file_location), parse with astroid, and return 
        the module.
        """
        with open(file_location) as f:
            content = f.read()
        return self.get_string_as_module(content)

    def get_string_as_module(self, string):
        """Parse the string with astroid, and return the module.
        """
        return astroid.parse(string)

    def _assertSameness(self, expected, props):
        """If sequences are not equal, it is convenient to see each side.
        """
        try:
            self.assertEqual(expected, props)
        except AssertionError as e:
            logging.error('Compare:\n{}\n  actual: {}'.format('-'*70, props))
            logging.error('expected: {}'.format(expected))
            logging.error('(fromlineno, end_lineno, col_offset, end_col_offset)')
            raise e  # otherwise, test will always 'pass'

    def set_and_check(self, module, node_class, expected):
        """Example is either in a file, or provided as a string literal.
        """
        self.ending_transformer.visit(module)
        props = self.nodeng.check_endings(module, node_class)
        self._assertSameness(expected, props)

    def test_arguments(self):
        expected = [(1, 2, 8, 30)]
        example = 'examples/ending_locations/arguments.py'
        module = self.get_file_as_module(example)
        self.set_and_check(module, astroid.Arguments, expected)

    def test_assert(self):
        expected = [(1, 1, 0, 43), (2, 2, 0, 11)]
        example = 'examples/ending_locations/assert.py'
        module = self.get_file_as_module(example)
        self.set_and_check(module, astroid.Assert, expected)

    def test_assign(self):
        expected = [(1, 1, 0, 6)]
        example = '''x = 10'''
        module = self.get_string_as_module(example)
        self.set_and_check(module, astroid.Assign, expected)

    def test_assignattr(self):
        expected = [(3, 3, 8, 12)]
        example = 'nodes/AssignAttr.py'
        module = self.get_file_as_module(example)
        self.set_and_check(module, astroid.AssignAttr, expected)

    def test_const(self):
        expected = [(1, 1, 0, 6), (2, 2, 4, 6)]
        example = 'examples/ending_locations/const.py'
        module = self.get_file_as_module(example)
        self.set_and_check(module, astroid.Const, expected)

    def test_binop(self):
        """note: value of col_offset = 6, is weird but we didn't set it.
        first (depends on pre/postorder) binop is ((1 + 2) + 3), then (1 + 2)
        """
        expected = [(1, 1, 6, 9), (1, 1, 0, 5)]
        example = '''1 + 2 + 3'''
        module = self.get_string_as_module(example)
        self.set_and_check(module, astroid.BinOp, expected)

    # TODO: Many more test functions here...

if __name__ == '__main__':
    unittest.main()  # run tests
