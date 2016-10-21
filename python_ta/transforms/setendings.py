"""
Top-level functions to mutate the astroid nodes with `end_col_offset` and
`end_lineno` properties.

In astroid/astroid/transforms.py, functions are registered to types in the
`transforms` dictionary in the TransformVisitor class. The traversal at
line 83 eventually leads to the transform called on each node at line 36,
within the _transform method.

Astroid Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py

If possible, set the `end_col_offset` property by that of the node's last child.
"""
import astroid
from astroid.transforms import TransformVisitor
import logging


# These nodes have no children, and their end_lineno and end_col_offset
# attributes are set based on their string representation (according to astroid).
NODES_WITHOUT_CHILDREN = [
    astroid.AssignName,
    astroid.Break,
    astroid.Const,
    astroid.Continue,
    astroid.DelName,
    astroid.Ellipsis,
    astroid.Global,
    astroid.Import,
    astroid.ImportFrom,
    astroid.List,
    astroid.Name,
    astroid.Nonlocal,
    astroid.Pass,
    astroid.Yield
]

# These nodes have a child, and their end_lineno and end_col_offset
# attributes are set equal to those of their last child.
NODES_WITH_CHILDREN = [
    astroid.Assert,
    astroid.Assign,
    # TODO: This one identifies only the expression to the left of the period,
    # and not the name of the attribute.
    # Given 'self.name = 10', it will highlight 'self' rather than 'self.name'
    astroid.AssignAttr,
    # TODO: Include the 'async' keyword in expressions for all Async* nodes.
    astroid.AsyncFor,
    astroid.AsyncFunctionDef,
    astroid.AsyncWith,
    # TODO: Same problem as AssignAttr (attribute missing)
    astroid.Attribute,
    astroid.AugAssign,
    astroid.Await,
    astroid.BinOp,
    astroid.BoolOp,
    # TODO: missing right parens
    astroid.Call,
    astroid.ClassDef,
    astroid.Compare,
    astroid.Comprehension,
    # TODO: missing right parens (note: only if decorator takes args)
    astroid.Decorators,
    # TODO: missing keyword 'del' and attribute name
    astroid.DelAttr,
    astroid.Delete,
    # TODO: missing right }
    astroid.Dict,
    # TODO: missing right }
    astroid.DictComp,
    astroid.ExceptHandler,
    # TODO: missing *both* outer brackets
    astroid.ExtSlice,
    # TODO: missing right paren
    astroid.Expr,
    astroid.For,
    astroid.FunctionDef,
    # TODO: missing *both* outer parens
    astroid.GeneratorExp,
    # TODO: need to fix elif (start) col_offset
    astroid.If,
    astroid.IfExp,
    # TODO: missing *both* outer brackets
    astroid.Index,
    # TODO: would be good to see the name of the keyword as well
    astroid.Keyword,
    astroid.Lambda,
    # TODO: missing *both* outer brackets
    astroid.ListComp,
    astroid.Module,
    astroid.Raise,
    astroid.Return,
    # TODO: missing right }
    astroid.Set,
    # TODO: missing right }
    astroid.SetComp,
    # TODO: missing *both* outer brackets
    astroid.Slice,
    astroid.Starred,
    # TODO: missing right ]
    astroid.Subscript,
    astroid.TryExcept,
    astroid.TryFinally,
    # TODO: missing *both* outer parens
    astroid.Tuple,
    astroid.UnaryOp,
    astroid.While,
    astroid.With,
    astroid.YieldFrom
]


class NodeDataStore():
    """Collect data and log at end of all tests."""
    def __init__(self):
        """Store data without dupes."""
        self._storage = set()

        # Question: do we want to move logger to its own module, in a utils directory?
        # Recall: the `logging` namespace is in the global scope.
        log_format = '%(asctime)s %(levelname)s %(message)s'
        log_date_time_format = '%Y-%m-%d %H:%M:%S'  # removed millis
        log_filename = 'python_ta/transforms/setendings_log.log'
        logging.basicConfig(format=log_format, datefmt=log_date_time_format, 
                            filename=log_filename, level=logging.INFO)

    def dump(self, prefix=''):
        """Log stored data in a simple csv format."""
        if prefix is not '':
            prefix += ' '  # add space after
        logging.info('{}{}'.format(prefix, ','.join(sorted(list(self._storage)))))

    def write(self, message):
        """Write message to a log file."""
        logging.info(message)

    def store(self, node):
        """Store node to data structure so the dump joins related items instead
        of having many separate messages."""
        self._storage.add(node)

# Global to expose to importing modules, and the transform functions.
node_data_store = NodeDataStore()


def init_register_ending_setters():
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.
    """
    ending_transformer = TransformVisitor()

    # Check consistency of astroid-provided fromlineno and col_offset attributes.
    for node_class in astroid.ALL_NODE_CLASSES:
        ending_transformer.register_transform(
            node_class,
            fix_start_attributes,
            lambda node: node.fromlineno is None or node.col_offset is None)

    # Ad hoc transformations
    ending_transformer.register_transform(astroid.Arguments, fix_start_attributes)
    ending_transformer.register_transform(astroid.Arguments, set_arguments)

    for node_class in NODES_WITH_CHILDREN:
        ending_transformer.register_transform(node_class, set_from_last_child)
    for node_class in NODES_WITHOUT_CHILDREN:
        ending_transformer.register_transform(node_class, set_without_children)

    # TODO: investigate these nodes, and create tests/transforms/etc when found.
    ending_transformer.register_transform(astroid.DictUnpack, discover_nodes)
    ending_transformer.register_transform(astroid.EmptyNode, discover_nodes)
    ending_transformer.register_transform(astroid.Exec, discover_nodes)
    ending_transformer.register_transform(astroid.Print, discover_nodes)
    ending_transformer.register_transform(astroid.Repr, discover_nodes)
    return ending_transformer


# Transform functions.
# These functions are called on individual nodes to either fix the
# `fromlineno` and `col_offset` properties of the nodes,
# or to set the `end_lineno` and `end_col_offset` attributes for a node.

def discover_nodes(node):
    """Log to file and console when an elusive node is encountered, so it can
    be classified, and tested..
    """
    # Some formatting for the code output
    output = [line for line in node.statement().as_string().strip().split('\n')]
    output = ['=' * 40] + output + ['=' * 40]
    message = '>>>>> Found elusive {} node. Context:\n\t{}'.format(node, '\n\t'.join(output))
    # Print to console, and log for persistence.
    print('\n' + message)
    node_data_store.write(message)


def fix_start_attributes(node):
    """Some nodes don't always have the `col_offset` property set by Astroid:
    Comprehension, ExtSlice, Index, Keyword, Module, Slice.
    """
    assert node.fromlineno is not None, \
            'node {} doesn\'t have fromlineno set.'.format(node)

    # Log when this function is called.
    node_data_store.store(str(node)[:-2])

    try:
        first_child = next(node.get_children())
        if node.fromlineno is None:
            node.fromlineno = first_child.fromlineno
        if node.col_offset is None:
            node.col_offset = first_child.col_offset

    except StopIteration:
        # No children. Go to the enclosing statement and use that.
        # This assumes that statement nodes will always have these attributes set.
        statement = node.statement()
        assert statement.fromlineno is not None and statement.col_offset is not None, \
            'Statement node {} doesn\'t have start attributes set.'.format(statement)

        if node.fromlineno is None:
            node.fromlineno = statement.fromlineno
        if node.col_offset is None:
            node.col_offset = statement.col_offset


def set_from_last_child(node):
    """Populate ending locations for astroid node based on its last child.

    Preconditions:
      - `node` must have a `last_child` (node).
      - `node` has col_offset property set.
    """
    last_child = _get_last_child(node)

    assert (last_child is not None and
            last_child.end_lineno is not None and
            last_child.end_col_offset is not None),\
        'ERROR: last_child is missing or is missing attributes.'

    node.end_lineno, node.end_col_offset = last_child.end_lineno, last_child.end_col_offset


def set_without_children(node):
    """Populate ending locations for nodes that are guaranteed to never have
    children. E.g. Const.

    These node's end_col_offset are currently assigned based on their
    computed string representation. This may differ from their actual
    source code representation, however (mainly whitespace).

    Precondition: `node` must not have a `last_child` (node).
    """
    node.end_lineno = node.fromlineno
    node.end_col_offset = node.col_offset + len(node.as_string())


def set_arguments(node):
    """astroid.Arguments node is missing the col_offset, and has children only
    sometimes.
    Arguments node can be found in nodes: FunctionDef, Lambda.
    """
    if _get_last_child(node):
        set_from_last_child(node)
    else:  # node does not have children.
        # TODO: this should be replaced with the string parsing strategy
        node.end_lineno, node.end_col_offset = node.fromlineno, node.col_offset


def _get_last_child(node):
    """Returns the last child node, or None.
    Some nodes' last_child() attribute not set, e.g. astroid.Arguments.
    """
    if node.last_child():
        return node.last_child()
    else:
        # Get the first child from the `get_children` generator.
        skip_to_last_child = None  # save reference to last child.
        for skip_to_last_child in node.get_children():
            pass  # skip to last
        return skip_to_last_child  # postcondition: node, or None.
