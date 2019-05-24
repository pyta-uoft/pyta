import sys
import astroid
from astroid.node_classes import NodeNG
from graphviz import Graph
from typing import *
from typing import ForwardRef
from python_ta.typecheck.base import _TNode, TypeFail
from python_ta.transforms.type_inference_visitor import TypeInferer
from tests.custom_hypothesis_support import _parse_text


USAGE = 'Usage: python -m sample_usage.draw_tnodes <your-file.py>'


def _type_str(type):
    if isinstance(type, TypeVar) or isinstance(type, _GenericAlias) or \
            type.__class__.__name__ == '_Any' or \
            isinstance(type, ForwardRef) or type is None:
        return str(type).replace('typing.', '')
    elif getattr(type, '__origin__', None) is Union:
        trimmed_args = []
        for arg in type.__args__:
            if not isinstance(arg, _GenericAlias):
                trimmed_args.append(_type_str(arg))
            else:
                break
        if len(trimmed_args) == 0:
            trimmed_args.append(_type_str(type.__args__[0]))
        if len(trimmed_args) != len(type.__args__):
            trimmed_args.append('...')
        return 'Union[%s]' % ', '.join(trimmed_args)
    else:
        return type.__name__


def _find_type_fail(ast_node):
    if hasattr(ast_node, 'inf_type') and isinstance(ast_node.inf_type, TypeFail):
        return ast_node.inf_type
    else:
        for child in ast_node.get_children():
            child_res = _find_type_fail(child)
            if child_res is not None:
                return child_res
    return None


def gen_graph_from_nodes(nodes, type_fail=None):
    graph = Graph(format='png', strict=True)
    graph.node_attr['fontname'] = 'Courier New'
    graph.edge_attr['fontname'] = 'Courier New'
    for node in nodes:
        graph.node(_type_str(node.type),
                   '{type: %s|ast_node: %s|parent\'s type: %s}' %
                   (_type_str(node.type),
                    node.ast_node.as_string().replace('<', '\\<').replace('>', '\\>')
                        if node.ast_node else 'None',
                    _type_str(node.parent.type) if node.parent else 'NA'),
                   shape='record', style='rounded')
        for neighb, ctx_node in node.adj_list:
            graph.edge(_type_str(node.type), _type_str(neighb.type),
                       label=(f' {ctx_node.as_string()}' if ctx_node else ''))
    if type_fail:
        graph.node('tf',
                   '{TypeFail|src_node: %s}' %
                   (type_fail.src_node.as_string().replace('<', '\\<').replace('>', '\\>')
                        if type_fail.src_node else 'None'), shape='record')
        graph.edge('tf', _type_str(type_fail.tnode1.type), style='dashed')
        graph.edge('tf', _type_str(type_fail.tnode2.type), style='dashed')
    graph.view('tnode_graph')


def gen_graph_from_source(source: Union[str, NodeNG]):
    module, inferer = _parse_text(source)
    gen_graph_from_nodes(inferer.type_constraints._nodes, _find_type_fail(module))


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(USAGE)
        exit()

    with open(sys.argv[1]) as file:
        source = file.read()
        gen_graph_from_source(source)
