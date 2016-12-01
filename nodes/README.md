# Astroid Node Documentation

The modules in this directory exist to explain the attributes (and sometimes 
the role) of every node used by astroid.
Since astroid often have different attributes than the built-in ast module,
we have taken care to document all these different nodes here.

A notable exception is the Module node, which is omitted even from Astroid's 
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

In the Astroid documentation here, we often use the 
`Expr` and `Statement` names to represent expression and statement nodes, where 
nodes in each category play similar roles in certain situations. For example, 
`Expr` nodes can often be assigned to and values can be loaded from them. 
On the other hand, `Statement` nodes are standalone lines (or blocks) of code that 
usually compose the body of a parent node.

### `Statement` Nodes

* Assert
* Assign
* AsyncFor
* AsyncFunctionDef
* AsyncWith
* AugAssign
* Break
* ClassDef
* Continue
* Delete
* Expr (when enclosing an Expr-type node)
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

* Attribute  (see [below](#expression-context))
* Await
* BinOp
* BoolOp
* Call
* Compare
* Const
* DelAttr  (see [below](#expression-context))
* DelName  (see [below](#expression-context))
* Dict
* DictComp
* Ellipsis
* GeneratorExp
* IfExp
* Lambda
* ListComp
* Name  (see [below](#expression-context))
* Set
* SetComp
* UnaryOp
* Yield
* YieldFrom

These expression nodes are also assignable (can be the target of an Assign, etc.):

* AssignAttr  (see [below](#expression-context))
* AssignName  (see [below](#expression-context))
* List
* Starred
* Subscript
* Tuple

### Expression Context

All *assignable* Python and Astroid AST nodes have an attribute called `ctx` that is used
to indicate the context in which the node appears, and may have a value of 
`Load`, `Store`, or `Del`. (To refer to these collectively, our Astroid docs 
often refer to an `expr_context` type of node, so please do not be confused
when you see that notation.)

Interestingly, Astroid has two differences from Python builtin ASTs with regards 
to expression contexts of assignable nodes: the `Name` and `Attribute` nodes. 
These nodes do not have a `ctx` attribute; instead, the Astroid developers made 
the decision to split each use of the `Name` and `Attribute` nodes in 
different contexts into completely new node types. That is why the assignable
nodes listed above include `AssignAttr` and `AssignName`. See the table below
for more details.

Node and Context | Python version | Astroid version
---------------- | -------------- | ---------------
`Attribute` in `Load` | `Attribute` with `ctx=Load` | Simple `Attribute` node
`Attribute` in `Store` | `Attribute` with `ctx=Store` | `AssignAttr` node
`Attribute` in `Del` | `Attribute` with `ctx=Del` | `DelAttr` node
`Name` in `Load` | `Name` with `ctx=Load` | Simple `Name` node
`Name` in `Store` | `Name` with `ctx=Store` | `AssignName` node
`Name` in `Del` | `Name` with `ctx=Del` | `DelName` node

For more information about this change, please see the original issue made 
by the Astroid developers: https://github.com/PyCQA/astroid/issues/267#issuecomment-163119276
