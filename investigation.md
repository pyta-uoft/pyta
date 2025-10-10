# Investigation

## Table of Contents

- [Investigation into New Astroid Attributes](#investigation-into-new-astroid-attributes)
- [Examples on Primitive Type Nodes](#examples-on-primitive-type-nodes)
- [Removal of redundant custom logic](#removal-of-redundant-custom-logic)
- [Conclusion](#conclusion)

## Investigation into New Astroid Attributes

Astroid provides built-in "end location" attributes. These attributes are:

1. `end_lineno`: The 1-indexed line number where the node ends.
2. `end_col_offset`: The 0-indexed column offset where the node ends. This value is after the last symbol of the code represented by the node.

Usage examples:

```python
src = """
x = 10
while x < 21: #@
    x += 1
    print(x)
"""


if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    lineno, colno = node.end_lineno, node.end_col_offset
```

These attributes are part of the base NodeNG class, which is the foundation for all AST node classes in astroid.

## Examples on Primitive Type Nodes

Here is the list of primitive nodes in Astroid ("nodes without children"):

1. Const
2. AssignName
3. Name
4. DelName
5. Break
6. Continue
7. Global
8. Import
9. ImportFrom
10. Nonlocal
11. Pass

### 1. Const

```python
src ="""
y = 21
z = y
x = 10 #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    const = node.value # Extract the primitive Const node corresponding to 10
    assert const.lineno == 4 and const.col_offset == 4
    assert const.end_lineno == 4 and const.end_col_offset == 6
```

As we can see, Astroid correctly identifies the fact that the `Const` node end location is line 4 / offset 6.

### 2. AssignName

```python
src ="""
y = 21
z = y
x = 10 #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assign_name = node.targets[0] # Extract the primitive AssignName node corresponding to x
    assert assign_name.lineno == 4 and assign_name.col_offset == 0
    assert assign_name.end_lineno == 4 and assign_name.end_col_offset == 1
```

As we can see, Astroid correctly identifies the fact that the `AssignName` node end location is line 4 / offset 1.

### 3. Name

```python
src = """x = 10
foo(x) #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    name = node.func # Extract the primitive Name node corresponding to 'foo'
    assert name.lineno == 2 and name.col_offset == 0
    assert name.end_lineno == 2 and name.end_col_offset == 3
```

As we can see, Astroid correctly identifies the fact that the `Name` node end location is line 2 / offset 3.

### 4. DelName

```python
src = """x = 10
del x #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    delete = node.targets[0] # Extract the DelName node corresponding to x
    assert delete.lineno == 2 and delete.col_offset == 4
    assert delete.end_lineno == 2 and delete.end_col_offset == 5
```

As we can see, Astroid correctly identifies the fact that the `DelName` node end location is line 2 / offset 5

### 5. Break

```python
src = """x = 10
while x:
    break #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 3 and node.col_offset == 4
    assert node.end_lineno == 3 and node.end_col_offset == 9
```

As we can see, Astroid correctly identifies the fact that the `Break` node end location is line 3 / offset 9

### 6. Continue

```python
src = """
for i in range(10):
    if i < 10:
        continue #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 4 and node.col_offset == 8
    assert node.end_lineno == 4 and node.end_col_offset == 16
```

As we can see, Astroid correctly identifies the fact that the `Continue` node end location is line 4 / offset 16

### 7. Global

```python
src = """
global x #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 2 and node.col_offset == 0
    assert node.end_lineno == 2 and node.end_col_offset == 8
```

As we can see, Astroid correctly identifies the fact that the `Global` node end location is line 2 / offset 8

### 8. Import

```python
src = """
import astroid #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 2 and node.col_offset == 0
    assert node.end_lineno == 2 and node.end_col_offset == 14
```

As we can see, Astroid correctly identifies the fact that the `Import` node end location is line 2 / offset 14

### 9. ImportFrom

```python
src = """
from astroid import NodeNG #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 2 and node.col_offset == 0
    assert node.end_lineno == 2 and node.end_col_offset == 26
```

As we can see, Astroid correctly identifies the fact that the `Import` node end location is line 2 / offset 26

### 10. Nonlocal

```python
src = """
nonlocal x, y #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 2 and node.col_offset == 0
    assert node.end_lineno == 2 and node.end_col_offset == 13
```

As we can see, Astroid correctly identifies the fact that the `Nonlocal` node end location is line 2 / offset 13

### 11. Pass

```python
src = """
while True:
    pass #@
"""
if __name__ == "__main__":
    import astroid

    node = astroid.extract_node(src)
    assert node.lineno == 3 and node.col_offset == 4
    assert node.end_lineno == 3 and node.end_col_offset == 8
```

As we can see, Astroid correctly identifies the fact that the `Pass` node end location is line 3 / offset 8

## Removal of redundant custom logic

With the previous part in mind, it is clear that we can remove at least the `set_without_children` transformation.
In fact, I verified that after removing all instances of `set_without_children` in `setendings.py`, all 58 tests still hold! That's a promising result.

Next, let's take a look at the `NODES_REQUIRING_SOURCE` list in `setendings.py`. In short, the nodes in this list have their end
locations set by the helper `end_setter_from_source`. However, looking more closely, we notice a lot of nodes within this list do not
need their end locations modified or set (due to it already being correctly set by Python's AST traversal logic). Specifically, all 58 tests will still pass if we remove the following nodes:

```python
NODES_REQUIRING_SOURCE = [
    # (nodes.AsyncFor, _keyword_search("async"), None),
    # (nodes.AsyncFunctionDef, _keyword_search("async"), None),
    # (nodes.AsyncWith, _keyword_search("async"), None),
    (nodes.Call, None, _token_search(")")),
    (nodes.DelAttr, _keyword_search("del"), None),
    (nodes.DelName, _keyword_search("del"), None),
    # (nodes.Dict, None, _token_search("}")),
    # (nodes.DictComp, None, _token_search("}")),
    # (nodes.Expr, _token_search("("), _token_search(")")),
    (nodes.GeneratorExp, _token_search("("), _token_search(")")),
    # (nodes.If, _keyword_search("elif"), None),
    # (nodes.Keyword, _is_arg_name, None),
    (nodes.List, _token_search("["), _token_search("]")),
    # (nodes.ListComp, _token_search("["), _token_search("]")),
    # (nodes.Set, None, _token_search("}")),
    # (nodes.SetComp, None, _token_search("}")),
    (nodes.Slice, _token_search("["), None),
    (nodes.Tuple, None, _token_search(",")),
]
```

Furthermore, the same can be done with `NODES_WITH_CHILDREN`. By removing the following nodes from the list, all 58 tests still pass. This means
that the end location attributes are already correctly set by Python's AST traversal logic.

```python
NODES_WITH_CHILDREN = [
    # nodes.Assert,
    # nodes.Assign,
    # nodes.AsyncFor,
    # nodes.AsyncFunctionDef,
    # nodes.AsyncWith,
    # nodes.AugAssign,
    # nodes.Await,
    # nodes.BinOp,
    # nodes.BoolOp,
    nodes.Call,
    # nodes.ClassDef,
    # nodes.Compare,
    nodes.Comprehension,
    # nodes.Decorators,
    # nodes.Delete,
    # nodes.ExceptHandler,
    # nodes.For,
    # nodes.FormattedValue,
    # nodes.FunctionDef,
    # nodes.GeneratorExp,
    # nodes.If,
    # nodes.IfExp,
    # nodes.Keyword,
    # nodes.Lambda,
    # nodes.List,
    nodes.Module,
    # nodes.Raise,
    # nodes.Return,
    # nodes.Starred,
    # nodes.Subscript,
    # nodes.Try,
    # nodes.UnaryOp,
    # nodes.While,
    # nodes.With,
    # nodes.YieldFrom,
]
```

Additionally, after some more investigation, we notice that we can remove the `fix_subscript` transformer.
All tests still pass! However, the same cannot be said about:

1. `fix_slice`, due to edge cases where the slice node doesn't have children (E.g "[:]", "[::]", "[:][:]", "[::][::]")
2. `fix_argument`, due to python / astroid not setting end location attributes by default

Finally, let's tackle `end_setter_from_source` and `_add_parens`.

### Looking deeper into `end_setter_from_source`

This helper sets the end location of a node from source using the location of its child. I noticed that the
following code can be simplified from this:

```python
if not hasattr(node, "end_col_offset") or isinstance(node, nodes.Tuple):
    set_from_last_child(node)
```

To this:

```python
if isinstance(node, nodes.Tuple):
    set_from_last_child(node)
```

This is due to the fact that the argument node (node with no end location attributes set by Astroid / Python) has already
been modified by `fix_argument`. Hence, this check is not necessary and all tests still pass!

For the next change, we can notice that the following code can be simplified from this:

```python
# Search each character
for j in range(len(source_code[i])):
    if source_code[i][j] == "#":
        break  # skip over comment lines
    if pred(source_code[i], j, node):
        node.end_col_offset, node.end_lineno = j + 1, i + 1
        return node
    # only consume inert characters.
    elif source_code[i][j] not in CONSUMABLES:
        return node
```

To this:

```python
# Search each character
for j in range(len(source_code[i])):
    if source_code[i][j] == "#":
        break  # skip over comment lines
    if pred(source_code[i], j, node):
        node.end_col_offset = j + 1
        return node
    # only consume inert characters.
    elif source_code[i][j] not in CONSUMABLES:
        return node
```

All test still pass! Note, the reason behind this change has been briefly talked about in the previous iteration of this report.

### Looking deeper into `_add_parens`

Sadly, this function NEEDS to mutate the end-location (as well as the start-location) attributes to ensure that the location attributes are correct.

## Execution time difference

Performance analysis (via `cProfile`) shows a slight improvement after refactoring:

| Metric | Master   | Curr. Branch |
|--------|----------|--------------|
| **Average time** | 3.1734 s | 3.0243 s     |
| **Min time** | 2.8704 s | 2.8436 s     |
| **Max time** | 4.1178 s | 4.1256 s     |
| **Std deviation** | 0.4436 s | 0.3706 s     |
| **Average function calls** | 2,453,884 | 2,453,506    |


While `cProfile` results can vary slightly due to system conditions, these numbers suggest that the refactoring reduced overall function calls and slightly improved runtime performance.

## Conclusion

> **Note:** In my previous investigation, I raised concerns about nodes spanning multiple lines. This is no longer an issue in the current implementation, as `add_parens` and `end_setter_from_source` now correctly handle the cases that could previously cause problems.

- all 58 tests passed
- minimal amount of custom code PythonTA needs to set endings properly reached (I believe...)
- Refactored `setendings.py` and pushed changes
- Reduced overall function calls and slightly improved runtime performance
- task completed?
