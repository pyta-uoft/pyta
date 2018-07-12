import sys
from typing import *
from typing import CallableMeta, GenericMeta, TupleMeta, _ForwardRef, IO
import typing
import astroid


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
    '-': '__sub__',
    '*': '__mul__',
    '//': '__floordiv__',
    '%': '__mod__',
    '/': '__truediv__',
    '**': '__pow__',
    '&': '__and__',
    '^': '__xor__',
    '|': '__or__',
    '<<': '__lshift__',
    '>>': '__rshift__',
    '==': '__eq__',
    '!=': '__ne__',
    '<': '__lt__',
    '<=': '__le__',
    '>': '__gt__',
    '>=': '__ge__',
    'in': '__contains__'
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

def _get_name(t: type) -> str:
    if isinstance(t, _ForwardRef):
        return t.__forward_arg__
    else:
        return t.__name__


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
    operand = node.operand.inf_type.getValue().__name__

    return (
        f'You cannot {op_name} {_correct_article(operand)}, {node.operand.as_string()}.'
    )


def _correct_article(noun : str) -> str:
    """Helper to return a noun with the correct article."""
    if noun.lower()[0] in 'aeiou':
        return 'an ' + noun
    else:
        return 'a ' + noun
