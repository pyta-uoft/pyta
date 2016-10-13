# Astroid Node Documentation

## Purpose

While the builtin Python AST module `ast` has excellent documentation both 
[officially](https://docs.python.org/3.5/library/ast.html) and [elsewhere](https://greentreesnakes.readthedocs.io/en/latest/), the [official Astroid AST documentation](http://astroid.readthedocs.io/en/latest/) is sorely lacking. 
Thus, this module and its docstrings exist to explain the attributes (and sometimes 
the role) of every\* node used by Astroid. 
\*A notable exception is the Module node, which is omitted even from Astroid's 
own node lists, since it is the parent node of every other node.

## Format

Every node file is an example (or several examples) that are carefully explained in
the file's docstring. Every docstring takes the format:

```python
"""
NodeName astroid node

Explanation of node in ASTs and in Python code generally. More obscure Python 
statements will have more detailed explanations.

Attributes:
    - attribute_name  (type)
        - explanation of attribute

Example:
    - attribute_name  -> example_value
"""
```

## Informal Grammar

While the Python AST module's [abstract grammar](https://docs.python.org/3.5/library/ast.html#abstract-grammar) is very well-defined, there is no 
such resource available for Astroid. However, using various resources (such 
as the original Python grammar, Green Tree Snakes documentation, Astroid 
source code, and string representations of Astroid ASTs), it is possible to
come to a rough understanding of how Astroid treats various nodes of similar 
types similarly. Thus, in the Astroid documentation here, we often use the 
`Expr` and `Stmt` names to represent expression and statement nodes, where 
nodes in each category play similar roles in certain sitations. For example, 
`Expr` nodes can often be assigned to and values can be loaded from them. 
On the other hand, `Stmt` nodes are standalone lines (or blocks) of code that 
usually compose the body of a parent node.
(The `Expr` type is actually represented in Astroid by the `Expr` node itself,
but there is no such `Stmt` node.)

### `Stmt` Nodes

* Assert
* Assign
* AssignAtr
* AssignName
* AsyncFor
* AsyncFunctionDef
* AsyncWith
* AugAssign
* Break
* ClassDef
* Continue
* DelAttr
* Delete
* DelName
* Expr (when appearing alone)
* For
* FunctionDef
* Global
* If
* Import
* ImportFrom
* Nonlocal
* Pass
* Raise
* Return
* TryExcept
* TryFinally
* While
* With

### `Expr` Nodes

* Await
* BinOp
* BoolOp
* Call
* Compare
* Constant
* Dict
* DictComp
* Ellipsis
* GeneratorExp
* IfExp
* Lambda
* ListComp
* Set
* SetComp
* UnaryOp
* Yield
* YieldFrom

These nodes are also assignable (can be the target of an Assign, etc.):

* Attribute
* List
* Name
* Starred
* Subscript
* Tuple

### Expression Context

Some Python or Astroid AST nodes have an attribute called `ctx` that is used
to indicate the context in which the node appears, and may have a value of 
`Load`, `Store`, or `Del`. To refer to these collectively, our Astroid docs 
often refer to an `expr_context` type of node, so please do not be confused
when you see that notation.
