from __future__ import annotations
from typing import *
from typing import _GenericAlias
import astroid
from astroid.node_classes import NodeNG
from python_ta.utils import _get_name, _gorg


###############################################################################
# Operator translations into dunder method name and English name.
###############################################################################
UNARY_TO_ENGLISH = {
    '+': 'apply unary + to',
    '-': 'negate',
    '~': 'take the bitwise inverse of'
}

UNARY_TO_METHOD = {
    '+': '__pos__',
    '-': '__neg__',
    '~': '__invert__'
}

BINOP_TO_ENGLISH = {
    '+': 'add',
    '-': 'subtract',
    '*': 'multiply',
    '//': 'use integer division with',
    '%': 'use modulus with',
    '/': 'use floating-point division with',
    '**': 'exponentiate',
    '&': 'use bitwise AND with',
    '^': 'use bitwise XOR with',
    '|': 'use bitwise OR with',
    '<<': 'apply a bitshift to the left',
    '>>': 'apply a bitshift to the right',
    '==': 'compare',
    '!=': 'compare',
    '<': 'compare',
    '<=': 'compare',
    '>': 'compare',
    '>=': 'compare',
    # TODO : 'is' and 'in'
    }

BINOP_TO_METHOD = {
    '+': '__add__',
    '+=': '__iadd__',
    '-': '__sub__',
    '-=': '__isub__',
    '*': '__mul__',
    '*=': '__imul__',
    '//': '__floordiv__',
    '//=': '__ifloordiv__',
    '%': '__mod__',
    '%=': '__imod__',
    '/': '__truediv__',
    '**': '__pow__',
    '**=': '__ipow__',
    '&': '__and__',
    '&=': '__iand__',
    '^': '__xor__',
    '^=': '__ixor__',
    '|': '__or__',
    '|=': '__ior__',
    '<<': '__lshift__',
    '<<=': '__ilshift__',
    '>>': '__rshift__',
    '>>==': '__irshift__',
    '==': '__eq__',
    '!=': '__ne__',
    '<': '__lt__',
    '<=': '__le__',
    '>': '__gt__',
    '>=': '__ge__',
    'in': '__contains__',
    'not in': '__contains__'
    }

BINOP_TO_REV_METHOD = {
    '+': '__radd__',
    '-': '__rsub__',
    '*': '__rmul__',
    '//': '__rfloordiv__',
    '%': '__rmod__',
    '/': '__rtruediv__',
    '**': '__rpow__',
    '&': '__rand__',
    '^': '__rxor__',
    '|': '__ror__',
    '<<': '__rlshift__',
    '>>': '__rrshift__',
    }

INPLACE_TO_BINOP = {
    '+=': '+',
    '-=': '-',
    '*=': '*',
    '//=': '//',
    '%=': '%',
    '**=': '*',
    '&=': '&',
    '^=': '^',
    '|=': '=',
    '<<=': '<<',
    '>>=': '>>'
}


###############################################################################
# Error message
###############################################################################
def error_message(tf: TypeFail) -> None:
    """Return an appropriate error message given an instance of TypeFailFunction."""
    if isinstance(tf.src_node, astroid.UnaryOp):
        return unaryop_error_message(tf.src_node)
    elif isinstance(tf.src_node, astroid.BinOp):
        return binop_error_message(tf.src_node)
    elif isinstance(tf.src_node, astroid.Subscript):
        return subscript_error_message(tf.src_node)
    else:
        return f'TypeFail: Invalid function call at {tf.src_node.as_string()}'


###############################################################################
# BinOp message
###############################################################################
# TODO: Convert this into dictionary
def binary_op_hints(op, args):
    """Return an appropriate 'hint' or suggestion given the binary operation and operand types."""
    if op == '+':
        if 'int' in args and 'str' in args:
            return "Perhaps you wanted to cast the integer into a string or vice versa?"


def binop_error_message(node: astroid.BinOp) -> str:
    op_name = BINOP_TO_ENGLISH[node.op]
    left_type = _get_name(node.left.inf_type.getValue())
    right_type = _get_name(node.right.inf_type.getValue())
    hint = binary_op_hints(node.op, [left_type, right_type]) or ''

    return (
        f'You cannot {op_name} {_correct_article(left_type)}, {node.left.as_string()}, '
        f'and {_correct_article(right_type)}, {node.right.as_string()}. '
        f'{hint}'
    )


###############################################################################
# UnaryOp message
###############################################################################
def unaryop_error_message(node: astroid.UnaryOp) -> str:
    op_name = UNARY_TO_ENGLISH[node.op]
    operand = _get_name(node.operand.inf_type.getValue())

    return (
        f'You cannot {op_name} {_correct_article(operand)}, {node.operand.as_string()}.'
    )


###############################################################################
# Subscript message
###############################################################################
def subscript_error_message(node: astroid.Subscript) -> str:
    # Accessing an element of a List with an incompatible index type (non-integers)
    subscript_concrete_type = (node.value.inf_type).getValue()
    if subscript_concrete_type is type(None):
        return f'NoneType is not subscriptable.'

    if not isinstance(subscript_concrete_type, _GenericAlias):
        subscript_gorg = subscript_concrete_type
    else:
        subscript_gorg = _gorg(subscript_concrete_type)

    if subscript_gorg is list:
        slice_type = _get_name(node.slice.inf_type.getValue())
        slice_val = node.slice.value
        slice_str = slice_val.as_string() if isinstance(slice_val, NodeNG) else str(slice_val)
        return f'You can only access elements of a list using an int. ' \
               f'You used {_correct_article(slice_type)}, {slice_str}.'
    elif subscript_gorg is tuple:
        slice_type = _get_name(node.slice.inf_type.getValue())
        slice_val = node.slice.value
        slice_str = slice_val.as_string() if isinstance(slice_val, NodeNG) else str(slice_val)
        return f'You can only access elements of a tuple using an int. ' \
               f'You used {_correct_article(slice_type)}, {slice_str}.'
    elif subscript_gorg is dict:
        slice_type = _get_name(node.slice.inf_type.getValue())
        slice_val = node.slice.value
        slice_str = slice_val.as_string() if isinstance(slice_val, NodeNG) else str(slice_val)
        return f'You tried to access an element of this dictionary using ' \
               f'{_correct_article(slice_type)}, {slice_str}, ' \
               f'but the keys are of type {_get_name(subscript_concrete_type.__args__[0])}.'
    else:
        return f'You make a type annotation with an incorrect subscript.'


def _correct_article(noun : str) -> str:
    """Helper to return a noun with the correct article."""
    if noun.lower()[0] in 'aeiou':
        return 'an ' + noun
    else:
        return 'a ' + noun
