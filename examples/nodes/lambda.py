"""
Lambda astroid node

Lambda is a minimal function definition that can be used inside an expression.

Attributes:
    - args  (Arguments)
        - The arguments for function lambda.
    - body  (NodeNG)
        - The body of function lambda. The body should be a single node.

Example 1:
    Lambda(
        args=Arguments(
            vararg=None,
            kwarg=None,
            args=[],
            defaults=[],
            kwonlyargs=[],
            posonlyargs=[],
            posonlyargs_annotations=[],
            kw_defaults=[],
            annotations=[],
            varargannotation=None,
            kwargannotation=None,
            kwonlyargs_annotations=[],
            type_comment_args=[],
            type_comment_kwonlyargs=[],
            type_comment_posonlyargs=[]),
        body=Const(value=3))


Example 2:
    Lambda(
        args=Arguments(
            vararg=None,
            kwarg=None,
            args=[AssignName(name='x'), AssignName(name='y')],
            defaults=[],
            kwonlyargs=[],
            posonlyargs=[],
            posonlyargs_annotations=[],
            kw_defaults=[],
            annotations=[None, None],
            varargannotation=None,
            kwargannotation=None,
            kwonlyargs_annotations=[],
            type_comment_args=[None, None],
            type_comment_kwonlyargs=[],
            type_comment_posonlyargs=[]),
        body=BinOp(
            op='+',
            left=Name(name='x'),
            right=Name(name='y')))


Type-checking:
    The inferred type is a Callable with arguments inferred from the body of the
    lambda expressions and whose return type is the inferred type of the body.
"""

# Example 1
lambda: 3

# Example 2
lambda x, y: x + y
