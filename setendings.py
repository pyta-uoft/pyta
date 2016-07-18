import astroid


# Helper functions to abstract common tasks. Global for now..
# TODO: Separate into module Class.
################################################################################
def _set_end_lineno(node):
    """Transform the property in-place.
    """
    node.end_lineno = node.lineno

def _set_end_lineno(node):
    """Transform the property in-place.
    Testing with simple, single-line things for now.
    Goal is to work on various multi-line nodes, with complicated nesting.
    """
    if node.tolineno is None:  # Guard.
        logging.error("⚠️ lineno is None at node: {}".format(node))
    node.end_lineno = node.tolineno

def _set_end_col_offset(node):
    """
    """
    pass


# Define the functions to transform the nodes.
# Mutate the nodes, adding the properties: `end_lineno`, `end_col_offset`.
################################################################################
def set_const(node):
    """Populate ending locations for Const nodes: astroid.Const
    Note: only Const node has .value property.
    Examples include: ints, None, True, False.
    """
    _set_end_lineno(node)
    node.end_col_offset = node.col_offset + len(str(node.value))


