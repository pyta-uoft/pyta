"""
Top-level functions to mutate the astroid nodes with `end_col_offset` and
`end_lineno` properties.

Where possible, the `end_col_offset` property is set by that of the node's last child.

    fromlineno
        - existing attribute
        - one-indexed
    end_lineno
        - new attribute
        - one-indexed
    col_offset
        - existing attribute
        - zero-indexed
        - located left of the first character
    end_col_offset
        - new attribute
        - zero-indexed
        - located right of the last character (essentially the string length)

In astroid/astroid/transforms.py, functions are registered to types in the
`transforms` dictionary in the TransformVisitor class. The traversal at
line 83 eventually leads to the transform called on each node at line 36,
within the _transform method.

Astroid Source:
https://github.com/PyCQA/astroid/blob/master/astroid/transforms.py
"""
import sys

import astroid
from astroid.node_classes import NodeNG
from astroid.transforms import TransformVisitor

CONSUMABLES = " \n\t\\"


# These nodes have no children, and their end_lineno and end_col_offset
# attributes are set based on their string representation (according to astroid).
# Goal: eventually replace the transforms for all the nodes in this list with the
# predicate technique that uses more robust approach using searching, rather than
# simple length of string.
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
    astroid.AsyncFor,
    astroid.AsyncFunctionDef,
    astroid.AsyncWith,
    astroid.AugAssign,
    astroid.Await,
    astroid.BinOp,
    astroid.BoolOp,
    astroid.Call,
    astroid.ClassDef,
    astroid.Compare,
    astroid.Comprehension,
    astroid.Decorators,
    astroid.Delete,
    astroid.ExceptHandler,
    astroid.For,
    astroid.FormattedValue,
    astroid.FunctionDef,
    astroid.GeneratorExp,
    astroid.If,
    astroid.IfExp,
    astroid.Index,
    astroid.Keyword,
    astroid.Lambda,
    astroid.List,
    astroid.Module,
    astroid.Raise,
    astroid.Return,
    astroid.Starred,
    astroid.Subscript,
    astroid.TryExcept,
    astroid.TryFinally,
    astroid.UnaryOp,
    astroid.While,
    astroid.With,
    astroid.YieldFrom
]


# Predicate functions, for setting locations based on source code.
# Predicates can only return a single truthy value, because of how its used in
# `astroid/transforms.py`
# ====================================================
def _token_search(token):
    """
    @type token: string
    @rtype: function
    """
    def _is_token(s, index, node):
        """Fix to include certain tokens such as a paren, bracket, or brace.
        @type s: string
        @type index: int
        @type node: Astroid node
        @rtype: bool
        """
        return s[index] == token
    return _is_token


def _keyword_search(keyword):
    """
    @type keyword: string
    @rtype: function
    """
    def _is_keyword(s, index, node):
        """Search for a keyword. Right-to-left.
        @type s: string
        @type index: int
        @type node: Astroid node
        @rtype: bool
        """
        return s[index : index+len(keyword)] == keyword
    return _is_keyword


def _is_attr_name(s, index, node):
    """Search for the name of the attribute. Left-to-right."""
    target_len = len(node.attrname)
    if index < target_len:
        return False
    return s[index-target_len+1 : index+1] == node.attrname


def _is_arg_name(s, index, node):
    """Search for the name of the argument. Right-to-left."""
    if not node.arg:
        return False
    return s[index : index+len(node.arg)] == node.arg


# Nodes the require the source code for proper location setting
# Elements here are in the form
# (node class, predicate for start | None, predicate for end | None)
NODES_REQUIRING_SOURCE = [
    (astroid.AssignAttr, None, _is_attr_name),
    (astroid.AsyncFor, _keyword_search('async'), None),
    (astroid.AsyncFunctionDef, _keyword_search('async'), None),
    (astroid.AsyncWith, _keyword_search('async'), None),
    (astroid.Attribute, None, _is_attr_name),
    (astroid.Call, None, _token_search(')')),
    (astroid.DelAttr, _keyword_search('del'), _is_attr_name),
    (astroid.DelName, _keyword_search('del'), None),
    (astroid.Dict, None, _token_search('}')),
    (astroid.DictComp, None, _token_search('}')),
    (astroid.Expr, _token_search('('), _token_search(')')),

    # TODO: use same behavior as Slice.
    (astroid.ExtSlice, _token_search('['), _token_search(']')),
    (astroid.GeneratorExp, _token_search('('), _token_search(')')),
    (astroid.If, _keyword_search('elif'), None),
    (astroid.Index, _token_search('['), _token_search(']')),
    (astroid.Keyword, _is_arg_name, None),
    (astroid.List, _token_search('['), _token_search(']')),
    (astroid.ListComp, _token_search('['), _token_search(']')),
    (astroid.Set, None, _token_search('}')),
    (astroid.SetComp, None, _token_search('}')),
    (astroid.Slice, _token_search('['), None),
    (astroid.Tuple, None, _token_search(',')),
]


def init_register_ending_setters(source_code):
    """Instantiate a visitor to transform the nodes.
    Register the transform functions on an instance of TransformVisitor.

    @type source_code: list of strings
    @rtype: TransformVisitor
    """
    ending_transformer = TransformVisitor()

    # Check consistency of astroid-provided fromlineno and col_offset attributes.
    for node_class in astroid.ALL_NODE_CLASSES:
        ending_transformer.register_transform(
            node_class,
            fix_start_attributes,
            lambda node: node.fromlineno is None or node.col_offset is None)

    # Ad hoc transformations
    ending_transformer.register_transform(astroid.BinOp, _set_start_from_first_child)
    ending_transformer.register_transform(astroid.ClassDef, _set_start_from_first_child)
    ending_transformer.register_transform(astroid.FunctionDef, _set_start_from_first_child)
    ending_transformer.register_transform(astroid.Tuple, _set_start_from_first_child)
    ending_transformer.register_transform(astroid.Arguments, fix_arguments(source_code))
    ending_transformer.register_transform(astroid.Slice, fix_slice(source_code))

    for node_class in NODES_WITHOUT_CHILDREN:
        ending_transformer.register_transform(node_class, set_without_children)
    for node_class in NODES_WITH_CHILDREN:
        ending_transformer.register_transform(node_class, set_from_last_child)

    if sys.version_info >= (3, 9):
        ending_transformer.register_transform(astroid.Subscript, fix_subscript(source_code))

    # Nodes where the source code must also be provided.
    # source_code and the predicate functions get stored in the TransformVisitor
    for node_class, start_pred, end_pred in NODES_REQUIRING_SOURCE:
        if start_pred is not None:
            ending_transformer.register_transform(
                node_class, start_setter_from_source(source_code, start_pred))
        if end_pred is not None:
            # This is for searching for a trailing comma after a tuple's final element
            if node_class is astroid.Tuple:
                ending_transformer.register_transform(
                    node_class, end_setter_from_source(source_code, end_pred, True))
            else:
                ending_transformer.register_transform(
                    node_class, end_setter_from_source(source_code, end_pred))

    # Nodes where extra parentheses are included
    ending_transformer.register_transform(astroid.BinOp, add_parens(source_code))
    ending_transformer.register_transform(astroid.Const, add_parens(source_code))
    ending_transformer.register_transform(astroid.Tuple, add_parens(source_code))

    return ending_transformer


# Transform functions.
# These functions are called on individual nodes to either fix the
# `fromlineno` and `col_offset` properties of the nodes,
# or to set the `end_lineno` and `end_col_offset` attributes for a node.
# ====================================================
def fix_slice(source_code):
    """
    The Slice node column positions are mostly set properly when it has (Const)
    children. The main problem is when Slice node doesn't have children.
    E.g "[:]", "[::]", "[:][:]", "[::][::]", ... yikes! The existing positions
    are sometimes set improperly to 0.
    """
    def _find_square_brackets(node):
        if _get_last_child(node):
            set_from_last_child(node)
            line_i = node.end_lineno - 1  # convert 1 to 0 index.
            char_i = node.end_col_offset
            has_children = True
        else:
            line_i = node.parent.value.end_lineno - 1  # convert 1 to 0 index.
            char_i = node.parent.value.end_col_offset
            has_children = False

        # Search the remaining source code for the "]" char.
        while char_i < len(source_code[line_i]) and source_code[line_i][char_i] != ']':
            if char_i == len(source_code[line_i]) - 1 or source_code[line_i][char_i] == '#':
                char_i = 0
                line_i += 1
            else:
                char_i += 1

        if not has_children:
            node.fromlineno, node.col_offset = line_i + 1, char_i
        node.end_lineno, node.end_col_offset = line_i + 1, char_i + 1

        return node

    return _find_square_brackets


def fix_subscript(source_code):
    """For a Subscript node.

    Need to include this because the index/extended slice is a value rather than
    a separate Index/ExtSlice in Python 3.9.
    """
    def _fix_end(node: astroid.Subscript) -> astroid.Subscript:
        if isinstance(node.slice, astroid.Slice):
            # In this case, the subscript node already contains the final ].
            return node

        # Search the remaining source code for the "]" char.
        if _get_last_child(node):
            set_from_last_child(node)
            line_i = node.end_lineno - 1  # convert 1 to 0 index.
            char_i = node.end_col_offset
        else:
            line_i = node.value.end_lineno - 1  # convert 1 to 0 index.
            char_i = node.value.end_col_offset

        while char_i < len(source_code[line_i]) and source_code[line_i][char_i] != ']':
            if char_i == len(source_code[line_i]) - 1 or source_code[line_i][char_i] == '#':
                char_i = 0
                line_i += 1
            else:
                char_i += 1

        node.end_lineno, node.end_col_offset = line_i + 1, char_i + 1
        return node

    return _fix_end


def fix_arguments(source_code):
    """For an Arguments node"""
    def _find(node: astroid.Arguments) -> astroid.Arguments:
        children = list(node.get_children())
        if children:
            fix_start_attributes(node)

        line_i = node.parent.fromlineno
        char_i = node.parent.col_offset
        for child in children:
            if line_i is None:
                line_i = child.end_lineno
                char_i = child.end_col_offset
            elif (line_i < child.end_lineno or
                  line_i == child.end_lineno and char_i < child.end_col_offset) :
                line_i = child.end_lineno
                char_i = child.end_col_offset

        line_i -= 1  # Switch to 0-indexing

        # left bracket if parent is FunctionDef, colon if Lambda
        if isinstance(node.parent, astroid.FunctionDef):
            end_char = ')'
        else:
            end_char = ':'

        while char_i < len(source_code[line_i]) and source_code[line_i][char_i] != end_char:
            if char_i == len(source_code[line_i]) - 1 or source_code[line_i][char_i] == '#':
                char_i = 0
                line_i += 1
            else:
                char_i += 1

        node.end_lineno, node.end_col_offset = line_i + 1, char_i

        # no children
        if children == []:
            node.fromlineno, node.col_offset = line_i + 1, char_i

        return node
    return _find


def fix_start_attributes(node):
    """Some nodes don't always have the `col_offset` property set by Astroid:
    Comprehension, ExtSlice, Index, Keyword, Module, Slice.
    """
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
        if statement is not node:
            if node.fromlineno is None:
                node.fromlineno = statement.fromlineno
            if node.col_offset is None:
                node.col_offset = statement.col_offset
        else:
            # Enclosing statement is same as node, also does not have attributes set
            if node.fromlineno is None:
                node.fromlineno = 0
            if node.col_offset is None:
                node.col_offset = 0
    return node


def _set_start_from_first_child(node):
    """Set the start attributes of this node from its first child."""
    try:
        first_child = next(node.get_children())
    except StopIteration:
        pass
    else:
        node.fromlineno = first_child.fromlineno
        node.col_offset = first_child.col_offset
    return node


def set_from_last_child(node):
    """Populate ending locations for astroid node based on its last child.

    Preconditions:
      - `node` must have a `last_child` (node).
      - `node` has col_offset property set.
    """
    last_child = _get_last_child(node)
    if not last_child:
        set_without_children(node)
        return node
    elif not hasattr(last_child, 'end_lineno'):  # Newly added for Slice() node.
        set_without_children(last_child)

    if last_child.end_lineno is not None:
        node.end_lineno = last_child.end_lineno
    if last_child.end_col_offset is not None:
        node.end_col_offset = last_child.end_col_offset
    return node


def set_without_children(node):
    """Populate ending locations for nodes that are guaranteed to never have
    children. E.g. Const.

    These node's end_col_offset are currently assigned based on their
    computed string representation. This may differ from their actual
    source code representation, however (mainly whitespace).

    Precondition: `node` must not have a `last_child` (node).
    """
    if not hasattr(node, 'end_lineno'):
        node.end_lineno = node.fromlineno
    # FIXME: using the as_string() is a bad technique because many different
    # whitespace possibilities that may not be reflected in it!
    if not hasattr(node, 'end_col_offset'):
        node.end_col_offset = node.col_offset + len(node.as_string())
    return node


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


def end_setter_from_source(source_code, pred, only_consumables=False):
    """Returns a *function* that sets ending locations for a node from source.

    The basic technique is to do the following:
      1. Find the ending locations for the node based on its last child.
      2. Starting at that point, iterate through characters in the source code
         up to and including the first index that satisfies pred.

    pred is a function that takes a string and index and returns a bool,
    e.g. _is_close_paren

    If only_consumables is True, the search halts when it reaches a non-consumable
    character that fails pred *on the first line*.
    TODO: really the behaviour should be the same for all lines searched for.
    """
    def set_endings_from_source(node):
        if not hasattr(node, 'end_col_offset'):
            set_from_last_child(node)

        # Initialize counters. Note: we need to offset lineno,
        # since it's 1-indexed.
        end_col_offset, lineno = node.end_col_offset, node.end_lineno - 1

        # First, search the remaining part of the current end line.
        for j in range(end_col_offset, len(source_code[lineno])):
            if source_code[lineno][j] == '#':
                break  # skip over comment lines
            if pred(source_code[lineno], j, node):
                node.end_col_offset = j + 1
                return node
            elif only_consumables and source_code[lineno][j] not in CONSUMABLES:
                return node

        # If that doesn't work, search remaining lines
        for i in range(lineno + 1, len(source_code)):
            # Search each character
            for j in range(len(source_code[i])):
                if source_code[i][j] == '#':
                    break  # skip over comment lines
                if pred(source_code[i], j, node):
                    node.end_col_offset, node.end_lineno = j + 1, i + 1
                    return node
                # only consume inert characters.
                elif source_code[i][j] not in CONSUMABLES:
                    return node
        return node

    return set_endings_from_source


def start_setter_from_source(source_code, pred):
    """Returns a *function* that sets start locations for a node from source.
    Recall `source_code`, `pred` are within the lexical scope of the returned function.

    The basic technique is to do the following:
      1. Find the start locations for the node (already set).
      2. Starting at that point, iterate through characters in the source code
         in reverse until reaching the first index that satisfies pred.

    pred is a function that takes a string and index and returns a bool,
    e.g. _is_open_paren
    """
    def set_start_from_source(node):
        # Initialize counters. Note: fromlineno is 1-indexed.
        col_offset, lineno = node.col_offset, node.fromlineno - 1

        # First, search the remaining part of the current start line
        for j in range(min(len(source_code[lineno]) - 1, col_offset), -1, -1):
            if pred(source_code[lineno], j, node):
                node.col_offset = j
                return node

        # If that doesn't work, search remaining lines
        for i in range(lineno - 1, -1, -1):
            # Search each character, right-to-left
            for j in range(len(source_code[i]) - 1, -1, -1):
                if pred(source_code[i], j, node):
                    node.end_col_offset, node.end_lineno = j, i + 1
                    return node
                # only consume inert characters.
                elif source_code[i][j] not in CONSUMABLES:
                    return node
        return node

    return set_start_from_source


def add_parens(source_code):
    def h(node):
        _add_parens(source_code)(node)

    return h


def _add_parens(source_code):
    def h(node):
        # Initialize counters. Note: fromlineno is 1-indexed.
        prev =  node.fromlineno, node.col_offset, node.end_lineno, node.end_col_offset
        while True:
            col_offset, lineno = node.col_offset, node.fromlineno - 1
            end_col_offset, end_lineno = node.end_col_offset, node.end_lineno - 1

            # First, search the remaining part of the current start line
            prev_char, new_lineno, new_coloffset = None, None, None
            for j in range(col_offset - 1, -1, -1):
                if source_code[lineno][j] in CONSUMABLES or source_code[lineno][j] == ',':
                    continue
                else:
                    prev_char, new_lineno, new_coloffset = source_code[lineno][j], lineno, j
                    break

            if prev_char is None:
                # Search remaining lines
                for i in range(lineno - 1, -1, -1):
                    # Search each character, right-to-left
                    for j in range(len(source_code[i]) - 1, -1, -1):
                        if source_code[i][j] in CONSUMABLES or source_code[i][j] == ',':
                            continue
                        else:
                            prev_char, new_lineno, new_coloffset = source_code[i][j], i, j

                            break
                    if prev_char is not None:
                        break

            if prev_char != '(':
                # No enclosing parentheses
                break

            # Now search for matching ')'
            next_char, new_end_lineno, new_end_coloffset = None, None, None
            for j in range(end_col_offset, len(source_code[end_lineno])):
                if source_code[end_lineno][j] == '#':
                    break  # skip over comment lines
                elif source_code[end_lineno][j] in CONSUMABLES:
                    continue
                else:
                    next_char, new_end_lineno, new_end_coloffset = source_code[end_lineno][j], end_lineno, j
                    break

            if next_char is None:
                # Search remaining lines
                for i in range(end_lineno + 1, len(source_code)):
                    # Search each character
                    for j in range(len(source_code[i])):
                        if source_code[i][j] == '#':
                            break  # skip over comment lines
                        elif source_code[i][j] in CONSUMABLES:
                            continue
                        else:
                            next_char, new_end_lineno, new_end_coloffset = source_code[i][j], i, j
                            break
                    if next_char is not None:
                        break

            if next_char != ')':
                break

            # At this point, an enclosing pair of parentheses has been found
            prev = node.fromlineno, node.col_offset, node.end_lineno, node.end_col_offset
            node.fromlineno, node.col_offset, node.end_lineno, node.end_col_offset =\
                new_lineno + 1, new_coloffset, new_end_lineno + 1, new_end_coloffset + 1

        # Go back by 1 set of parentheses if inside a function call.
        if isinstance(node.parent, astroid.Call) and len(node.parent.args) == 1:
            node.fromlineno, node.col_offset, node.end_lineno, node.end_col_offset = prev

        return node

    return h


# Make this module a pylint plugin
def register(linter):
    old_get_ast = linter.get_ast

    def new_get_ast(filepath, modname):
        ast = old_get_ast(filepath, modname)
        with open(filepath) as f:
            source_code = f.readlines()
        ending_transformer = TransformVisitor()
        register_transforms(source_code, ending_transformer)
        ending_transformer.visit(ast)
        return ast

    linter.get_ast = new_get_ast


def register_transforms(source_code, obj):
    # Check consistency of astroid-provided fromlineno and col_offset attributes.
    for node_class in astroid.ALL_NODE_CLASSES:
        obj.register_transform(
            node_class,
            fix_start_attributes,
            lambda node: node.fromlineno is None or node.col_offset is None)

    # Ad hoc transformations
    obj.register_transform(astroid.Arguments, fix_arguments(source_code))

    for node_class in NODES_WITH_CHILDREN:
        obj.register_transform(node_class, set_from_last_child)
    for node_class in NODES_WITHOUT_CHILDREN:
        obj.register_transform(node_class, set_without_children)

    # Nodes where the source code must also be provided.
    for node_class, start_pred, end_pred in NODES_REQUIRING_SOURCE:
        if start_pred is not None:
            obj.register_transform(
                node_class, start_setter_from_source(source_code, start_pred))
        if end_pred is not None:
            obj.register_transform(
                node_class, end_setter_from_source(source_code, end_pred))
