"""
Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py

"""

from astroid.transforms import TransformVisitor
import astroid
import unittest
import logging
from setendings import *

# Set the log level (DEBUG, ERROR, ...), and message format.
logging.basicConfig(format='', level=logging.ERROR)

class EndingVisitor(TransformVisitor):
    """Overriding some TransformVisitor to use the visit traversal, and other
    things for testing.
    """

    def __init__(self):
        super().__init__()
        # Keep a list rather than a set, because "too many" is wrong.
        self.props_check = []

    def _transform(self, node):
        """Value returned here is also returned by the visit() method in
        TransformVisitor.
        """
        if isinstance(node, astroid.Const):
            self.props_check.append([node.lineno, node.end_lineno, 
                                    node.col_offset, node.end_col_offset])
            logging.debug('Visiting node ' + str(node))
            logging.debug('\tLines {} to {}'.format(node.lineno, node.end_lineno))
            logging.debug('\tCols {} to {}'.format(node.col_offset, node.end_col_offset))
        return self.props_check


################################################################################
class TestEndingLocation(unittest.TestCase):
    """
    Testing the properties set on ast nodes: `end_lineno`, `end_col_offset`.

    Method explanations:
    ending_transformer.visit(module)
        Walk the given astroid *tree* and transform each encountered node
        *** Only the nodes which have transforms registered will actually
        be replaced or changed.
    
    ending_visitor.visit(module)
        Show that the transform worked.

    ending_transformer.register_transform(astroid.<Type>, <function_name>)
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

    def setUp(self):
        # A visitor to transform the nodes.
        self.ending_transformer = TransformVisitor()
        # A visitor to test the nodes property correctness.
        self.ending_visitor = EndingVisitor()
        # Register `transform(node)` function.
        self.ending_transformer.register_transform(astroid.Const, set_const)

    def _get_content_as_module(self, file_location):
        """Given a filepath (file_location), parse with astroid, and return 
        the module.
        """
        with open('examples/ending_locations/const.py') as f:
            content = f.read()
        return astroid.parse(content)

    def _are_equal(self, expected, props_assigned):
        """Check if two lists are equal. Not more items, and not less items.
        """
        pass

    def _all_props_set(self):
        """Check a file for whether all ending location properties have been 
        set.
        """

    # Test methods must start with 'test_', and pass in 'self'
    def test_const(self):
        expected = [[1, 1, 0, 6], [2, 2, 4, 6]]
        file_location = 'examples/ending_locations/const.py'
        module = self._get_content_as_module(file_location)
        self.ending_transformer.visit(module)  # transform
        props_assigned = self.ending_visitor.visit(module)  # check
        # logging.debug(props_assigned)
        self.assertEqual(props_assigned, expected)


if __name__ == '__main__':
    # TODO: turn this into a proper test
    # ending_transformer = TransformVisitor()

    # make an astroid object
    # with open('examples/ending_locations/const.py') as f:
    #     content = f.read()
    # module = astroid.parse(content)

    # Register `transform(node)` function to be applied on the given
    # astroid's `node_class`. Internally, appends the function to a
    # dictionary in the TransformVisitor class. The keys are the node types, so
    # each node must have been assigned/registered a transform function!!
    # The transform function may return a value which is then used to
    # substitute the original node in the tree.
    # params: node_class, transform function
    # ending_transformer.register_transform(astroid.Const, set_const)    

    # for node in module.body:
    #     print("node:", node)

    # Walk the given astroid *tree* and transform each encountered node
    # *** Only the nodes which have transforms registered will actually
    # be replaced or changed.
    # ending_transformer.visit(module)

    # Show that the mutation worked.
    # ending_visitor = EndingVisitor()
    # ending_visitor.visit(module)

    # run tests
    # unittest.main()
    suite = unittest.TestLoader().loadTestsFromTestCase(TestEndingLocation)
    unittest.TextTestRunner(verbosity=2).run(suite)



