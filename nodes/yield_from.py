"""
YieldFrom astroid node

This node represents the Python "yield from" statement, which functions
similarly to the "yield" statement except that the generator can delegate
some generating work to another generator.

Attributes:
    - value  (Expr)
        - The generator that this YieldFrom is delegating work to,
          which must be a generator expression (either a GeneratorExp node
          or an Expr node containing a generator expression).

Example (nested in Expr):
    FunctionDef(
        name='fun',
        doc=None,
        decorators=None,
        args=Arguments(
            vararg=None,
            kwarg=None,
            args=[AssignName(name='g')],
            defaults=[],
            kwonlyargs=[],
            posonlyargs=[],
            posonlyargs_annotations=[],
            kw_defaults=[],
            annotations=[None],
            varargannotation=None,
            kwargannotation=None,
            kwonlyargs_annotations=[],
            type_comment_args=[None],
            type_comment_kwonlyargs=[],
            type_comment_posonlyargs=[]),
        returns=None,
        body=[Expr(
            value=YieldFrom(
                value=Call(
                    func=Name(name='range'),
                    args=[Name(name='g')],
                    keywords=None)))])
"""

def fun(g):
    yield from range(g)
