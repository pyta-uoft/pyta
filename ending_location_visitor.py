"""
Astroid Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py

See class and method docstrings for explanations.

Run: python ending_location_visitor.py
"""

from sys import exit
from astroid.transforms import TransformVisitor
import astroid
import unittest
import logging
from setendings import *
from inspect_ast import visit_astroid

# Set the log level (DEBUG, ERROR, ...), and message format.
logging.basicConfig(format='', level=logging.DEBUG)


class EndingVisitor(TransformVisitor):
    """Subclass of TransformVisitor used for the visit() traversal, and other
    things just for testing, i.e. EndingVisitor subclass is independent of our
    linter functionality, so free to override the methods in this EndingVisitor 
    subclass.
    """

    def __init__(self):
        super().__init__()
        self.reset()

    def _transform(self, node):
        """Overridden method.
        Note: the value returned here is also returned by the visit() method in
        TransformVisitor.
        """
        if isinstance(node, self.node_type):  # check it is intended node type.
            try:
                self.props_check.append([node.lineno, node.end_lineno, 
                                    node.col_offset, node.end_col_offset])
            except AttributeError:
                # (with our message) raise again to also get traceback.
                raise AttributeError('''Make sure the properties are set in 
                    setendings.py and the function is registered with
                    ending_transformer.register_transform()''')

            # logging.debug('Visiting node ' + str(node))
            # logging.debug('\tLines {} to {}'.format(node.lineno, node.end_lineno))
            # logging.debug('\tCols {} to {}'.format(node.col_offset, node.end_col_offset))
        return self.props_check

    def type(self, node_type):
        """Set the type of node that we are inspecting. The type of node is
        compared against in a private method.
        """
        self.node_type = node_type
        return self;

    def reset(self):
        """Reset between test methods.
        """
        # Keep a list rather than a set, because "too many" is wrong.
        self.props_check = []
        self.node_type = None




################################################################################
class TestEndingLocation(unittest.TestCase):
    """
    Prove the `end_lineno`, `end_col_offset` properties are set on ast nodes.

    Method explanations:
    ending_transformer.visit(module)
        Walk the given astroid *tree* and transform each encountered node
        *** Only the nodes which have transforms registered will actually
        be replaced or changed.
    
    ending_visitor.visit(module)
        Show that the transform worked.

    ending_transformer.easy_register_transform(<astroid-node-name>),
    i.e.
    ending_transformer.register_transform(astroid.<Type>, <function>)
        Register `transform(node)` function to be applied on the given
        astroid's `node_class`. Internally, appends the function to a
        dictionary in the TransformVisitor class. The keys are the node types,
        each node must have been assigned/registered a transform function!!
        The transform function may return a value which is then used to
        substitute the original node in the tree.
        params: node_class, transform function

    We store the correct values as: 
        [lineno, end_lineno, col_offset, end_col_offset]
    """

    @classmethod
    def setUpClass(self):
        """A class method called before tests in an individual class run.
        setUpClass is called with the class as the only argument and must be
        decorated as a classmethod():"""
        
        # A visitor to transform the nodes.
        self.ending_transformer = TransformVisitor()

        # A visitor to test the nodes property correctness.
        self.ending_visitor = EndingVisitor()

        # Register all `transform(node)` functions here...
        # TODO: attach more nodes with their transform functions here.
        self.ending_transformer.register_transform(astroid.Arguments, set_general)

        self.ending_transformer.register_transform(astroid.Const, set_general)
        self.ending_transformer.register_transform(astroid.BinOp, set_general)














        
        

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
        self.ending_visitor.reset()

    def _get_file_as_module(self, file_location):
        """Given a filepath (file_location), parse with astroid, and return 
        the module.
        """
        with open(file_location) as f:
            content = f.read()
        return self._get_string_as_module(content)

    def _get_string_as_module(self, string):
        """Parse the string with astroid, and return the module.
        """
        return astroid.parse(string)

    def _are_equal(self, expected, props_assigned):
        """Check if two lists are equal. Not more items, and not less items.
        Note we cannot use a set because this would hide the inequality from
        repeated items.
        TODO: check for equality without respect to order of items in top-level.
        For example, the following lists are 'equal' for our purposes.
        [[1, 1, 0, 6], [2, 2, 4, 6]]
        [[2, 2, 4, 6], [1, 1, 0, 6]]
        """
        return expected == props_assigned

    def assertSameness(self, expected, props):
        """If sequences are not equal, it is convenient to see each side.
        """
        try:
            self.assertTrue(self._are_equal(expected, props))
        except AssertionError as e:
            logging.error('Compare:\n{}\nprops: {}'.format('-'*70, props))
            logging.error('expected: {}'.format(expected))
            logging.error('[lineno, end_lineno, col_offset, end_col_offset]')
            raise e  # otherwise, test will always 'pass'

    def _all_props_set(self):
        """Check a file for whether all ending location properties have been 
        set.
        """
        pass  # TODO
    
    def test_arguments(self):
        """[]
        """
        expected = [[1, 2, 8, 30]]
        example = '''def fun(so, many, arguments, and_some_are_long, soooooooooooooooooooo, 
                            wrappppppppppppppppppp):
                        pass
                 '''
        module = self._get_string_as_module(example)
        # visit_astroid(module)
        self.ending_transformer.visit(module)  # transform
        props = self.ending_visitor.type(astroid.Arguments).visit(module)  # check
        # logging.debug(props)
        self.assertSameness(expected, props)

    def test_const(self):
        """[]
        """
        expected = [[1, 1, 0, 6], [2, 2, 4, 6]]
        example = 'examples/ending_locations/const.py'
        module = self._get_file_as_module(example)
        # visit_astroid(module)
        self.ending_transformer.visit(module)  # transform
        props = self.ending_visitor.type(astroid.Const).visit(module)  # check
        # logging.debug(props)
        self.assertSameness(expected, props)

    def test_binop(self):
        # note 6 col_offset is weird, but we didn't set it.
        # first binop is (1 + 2), then ((1 + 2) + 3)
        expected = [[1, 1, 0, 5], [1, 1, 6, 9]]
        example = '''1 + 2 + 3
                 '''
        module = self._get_string_as_module(example)
        self.ending_transformer.visit(module)  # transform
        props = self.ending_visitor.type(astroid.BinOp).visit(module)  # check
        self.assertSameness(expected, props)


    # TODO: Many more test functions here...

















    





if __name__ == '__main__':
    unittest.main()  # run tests

