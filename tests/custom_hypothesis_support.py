import astroid
from astroid.node_classes import NodeNG
import hypothesis.strategies as hs
from hypothesis import assume
from python_ta.transforms.type_inference_visitor import TypeInferer
from keyword import iskeyword
from hypothesis import settings
from typing import Callable, Tuple, List, Union
settings.register_profile("pyta", settings(max_examples=10))


# Custom strategies for hypothesis testing framework
primitive_types = hs.sampled_from([
    hs.integers,
    hs.booleans,
    lambda: hs.floats(allow_nan=False, allow_infinity=False),
    hs.none,
    hs.text,
    hs.binary
])
primitive_values = primitive_types.flatmap(lambda s: s())


# Strategies for generating Indexes
index_types = hs.sampled_from([
    hs.integers,
    lambda: hs.text(alphabet="abcdefghijklmnopqrstuvwxyz", min_size=1)
])
index_values = index_types.flatmap(lambda s: s())


numeric_types = hs.sampled_from([
    hs.integers,
    lambda: hs.floats(allow_nan=False, allow_infinity=False)
])
numeric_values = numeric_types.flatmap(lambda s: s())


# Strategies for generating Binary Operators
non_bool_symbols = ['+', '-', '*', '//', '%', '/', '**', '&', '^', '|', '<<', '>>']
non_boolean_operator = hs.sampled_from(non_bool_symbols)
non_bool_unary_op = hs.sampled_from(['-', '+', '~'])

# Strategy for genearting Comparison Operators
comparator_symbols = ['<', '>']
comparator_operator = hs.sampled_from(comparator_symbols)
comparator_symbols_equality = ['==', '!=', '>=', '<=', 'is']
comparator_operator_equality = hs.sampled_from(comparator_symbols_equality)

# Strategy for generating Boolean Operators
binary_bool_operator = hs.sampled_from(['and', 'or'])
unary_bool_operator = hs.sampled_from(['not'])

# Strategies for generating builtin type names
builtin_types = [bool, bytearray, bytes, complex, dict, enumerate,
                    float, frozenset, int, list, set, str, tuple]
builtin_type = hs.sampled_from(builtin_types)
annotation = hs.sampled_from(builtin_types).map(lambda s: s.__name__)


def valid_identifier(**kwargs):
    """Return a strategy which generates a valid Python Identifier"""
    return hs.integers(min_value=0, max_value=1000).flatmap(
        lambda n: hs.just(f'x{n}')
    )


def homogeneous_list(**kwargs):
    """Return a strategy which generates a list of uniform type."""
    return primitive_types.flatmap(lambda s: hs.lists(s(), **kwargs))


def numeric_list(**kwargs):
    """Return a strategy which generates a list of uniform numeric types."""
    return numeric_types.flatmap(lambda s: hs.lists(s(), **kwargs))


def random_list(**kwargs):
    """Return a strategy which generates a random list."""
    return hs.lists(primitive_values, **kwargs)


def homogeneous_dictionary(**kwargs):
    """Return a strategy which generates a dictionary of uniform key:value type."""
    return index_types.flatmap(lambda s: hs.dictionaries(s(), s(),  **kwargs))


def random_dictionary(**kwargs):
    """Return a strategy which generates a random list."""
    return hs.dictionaries(primitive_values, primitive_values, **kwargs)


def random_dict_variable_homogeneous_value(**kwargs):
    """Return a strategy which generates a random dictionary of variable name and value"""
    return primitive_types.flatmap(lambda s: hs.dictionaries(valid_identifier(), s(), **kwargs))


homogeneous_iterable = hs.sampled_from([
        lambda: homogeneous_dictionary(min_size=1),
        lambda: homogeneous_list(min_size=1),
    ]).flatmap(lambda s: s())

heterogeneous_iterable = hs.sampled_from([
        lambda: random_dictionary(min_size=1),
        lambda: random_list(min_size=1),
        lambda: hs.sets(primitive_values, min_size=1)
    ]).flatmap(lambda s: s())


def _parse_dictionary_to_program(variables_dict):
    program = ""
    # parse dictionary into input program
    for variable_name in variables_dict:
        assume(not iskeyword(variable_name))
        program += variable_name + " = " + repr(variables_dict[variable_name]) + "\n"
    return program


# Strategies for generating Python ASTs.
# These are named after the corresponding nodes.
@hs.composite
def binop_node(draw, left=None, op=non_boolean_operator, right=None):
    left = left or const_node()
    right = right or const_node()
    node = astroid.BinOp(draw(op))
    node.postinit(draw(left), draw(right))
    return node


@hs.composite
def boolop_node(draw, value=None, op=binary_bool_operator, **kwargs):
    value = value or const_node()
    node = astroid.BoolOp(draw(op))
    if kwargs.get('min_size', 0) < 2:
        kwargs['min_size'] = 2
    node.postinit(draw(hs.lists(value, **kwargs)))
    return node


@hs.composite
def comprehension_node(draw, target=None, iter=None,
                       ifs=hs.just([])):
    target = target or const_node(valid_identifier())
    iter = iter or list_node()
    node = astroid.Comprehension()
    node.postinit(draw(target), draw(iter), draw(ifs))
    return node


@hs.composite
def const_node(draw, value=primitive_values):
    """Return a Const node with value drawn from <value>."""
    return astroid.Const(draw(value))


@hs.composite
def dict_node(draw, key=const_node(), value=const_node(), **kwargs):
    items = draw(hs.dictionaries(key, value, **kwargs)).items()
    node = astroid.Dict()
    node.postinit(items)
    return node


@hs.composite
def expr_node(draw, value=None):
    value = value or expr
    node = astroid.Expr()
    node.postinit(draw(value))
    return node


@hs.composite
def ifexp_node(draw, test=const_node(hs.booleans()),
               expr=const_node(), orelse=const_node()):
    # TODO: Add an option for whether expr and orelse strategies produce the same type.
    test = draw(test)
    expr = draw(expr)
    node = astroid.IfExp()
    node.postinit(test, expr, expr)
    return node


@hs.composite
def index_node(draw, value=const_node(hs.integers())):
    node = astroid.Index()
    node.postinit(draw(value))
    return node


@hs.composite
def set_node(draw, elt=const_node(), **kwargs):
    """Return a Set node with elements drawn from elt.
    """
    node = astroid.Set()
    node.postinit(draw(hs.sets(elt, **kwargs)))
    return node


@hs.composite
def setcomp_node(draw, elt=const_node(),
                 generators=hs.lists(comprehension_node(), min_size=1)):
    node = astroid.SetComp()
    node.postinit(draw(elt), draw(generators))
    return node


@hs.composite
def list_node(draw, elt=const_node(), **kwargs):
    """Return a List node with elements drawn from elt.
    """
    node = astroid.List()
    node.postinit(draw(hs.lists(elt, **kwargs)))
    return node


@hs.composite
def listcomp_node(draw, elt=const_node(),
                  generators=hs.lists(comprehension_node(), min_size=1)):
    node = astroid.ListComp()
    node.postinit(draw(elt), draw(generators))
    return node


@hs.composite
def slice_node(draw):
    lower = draw(hs.one_of(const_node(hs.integers()), hs.none()))
    upper = draw(hs.one_of(const_node(hs.integers()), hs.none()))
    step = draw(hs.one_of(const_node(hs.integers()), hs.none()))
    node = astroid.Slice()
    node.postinit(lower, upper, step)
    return node


@hs.composite
def subscript_node(draw, value=None, slice=index_node()):
    value = value or subscriptable_expr
    node = astroid.Subscript()
    node.postinit(
        draw(value),
        draw(slice)
    )
    return node


@hs.composite
def tuple_node(draw, elt=const_node, **kwargs):
    """Return a Tuple node with elements drawn from elt.
    """
    elts = draw(hs.lists(elt(), **kwargs, min_size=1))
    node = astroid.Tuple()
    node.postinit(elts)
    return node


@hs.composite
def unaryop_node(draw, op=hs.one_of(non_bool_unary_op, unary_bool_operator),
                 operand=const_node()):
    op = draw(op)
    operand = draw(operand)
    node = astroid.UnaryOp(op)
    node.postinit(operand)
    return node


@hs.composite
def simple_homogeneous_dict_node(draw, **kwargs):
    k = draw(primitive_types)
    v = draw(primitive_types)
    return draw(dict_node(
        const_node(k()),
        const_node(v()),
        **kwargs
    ))


@hs.composite
def simple_homogeneous_list_node(draw, **kwargs):
    t = draw(primitive_types)
    return draw(list_node(const_node(t()), **kwargs))


@hs.composite
def simple_homogeneous_set_node(draw, **kwargs):
    t = draw(primitive_types)
    homogeneous_set = draw(set_node(const_node(t()), **kwargs))
    assume(homogeneous_set.elts != set())
    return homogeneous_set



@hs.composite
def name_node(draw, name=None):
    if not name:
        node = astroid.Name(draw(valid_identifier()))
    else:
        node = astroid.Name(draw(name))
    return node


@hs.composite
def arguments_node(draw, annotated=False):
    n = draw(hs.integers(min_value=1, max_value=5))
    args = draw(hs.lists(name_node(None), min_size=n, max_size=n))
    if annotated:
        annotations = draw(hs.lists(name_node(annotation), min_size=n, max_size=n))
    else:
        annotations = None
    node = astroid.Arguments()
    node.postinit(
        args,
        None,
        None,
        None,
        annotations
    )
    return node


@hs.composite
def functiondef_node(draw, name=None, annotated=False, returns=False):
    name = name or draw(valid_identifier())
    args = draw(arguments_node(annotated))
    body = []
    returns_node = astroid.Return()
    arg_node, arg_type_node = draw(hs.sampled_from(list(zip(args.args, args.annotations))))
    if returns:
        returns_node.postinit(arg_node)
    else:
        returns_node.postinit(const_node(None))
    body.append(returns_node)
    node = astroid.FunctionDef(name=name)
    node.parent = astroid.Module('Default', None)
    node.postinit(
        args,
        body,
        None,
        arg_type_node
    )
    return node


expr = hs.one_of(
    const_node(),
    dict_node(min_size=1),
    list_node(min_size=1),
    tuple_node()
)

subscriptable_expr = hs.one_of(
    const_node(hs.text()),
    dict_node(min_size=1),
    list_node(min_size=1),
    tuple_node()
)


# Helper functions for testing
def _parse_text(source: Union[str, NodeNG], reset: bool = False) -> Tuple[astroid.Module, TypeInferer]:
    """Parse source code text and output an AST with type inference performed."""
    # TODO: apparently no literal syntax for empty set in Python3, also cannot do set()
    # TODO: Deal with special case later.
    # if isinstance(source, astroid.Set) and len(list(source.elts)) == 0:
    #     source = f'{set({})}'
    if not isinstance(source, str):  # It's an astroid node
        source = source.as_string()
    module = astroid.parse(source)
    type_inferer = TypeInferer()
    if reset:
        type_inferer.reset()
    type_inferer.environment_transformer().visit(module)
    type_inferer.type_inference_transformer().visit(module)
    return module, type_inferer


def _verify_type_setting(module, ast_class, expected_type):
    """Helper to verify nodes visited by type inference visitor of astroid class has been properly transformed."""
    result = [n.inf_type.getValue() for n in module.nodes_of_class(ast_class)]
    assert [expected_type] == result, f'{expected_type}, {result}'


def lookup_type(inferer: TypeInferer, node: NodeNG, name: str) -> type:
    """Given a variable name, return its concrete type in the closest scope relative to given node.
    Should be used only for testing purposes.
    """
    inf_type = inferer.lookup_inf_type(node, name)
    return inf_type.getValue()


def types_in_callable(inferer: TypeInferer, callable_function: Callable) -> Tuple[List[type], type]:
    """Return a tuple of types corresponding to the Callable function's arguments and return value, respectively.
    Used only for testing purposes.
    """
    arg_type_lst = [inferer.type_constraints.resolve(argument).getValue() for argument in callable_function.__args__]
    return arg_type_lst[:-1], arg_type_lst[-1]
