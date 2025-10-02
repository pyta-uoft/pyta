# Investigation

## Table of Contents

- [Investigation into New Astroid Attributes](#investigation-into-new-astroid-attributes)
- [Examples on Primitive Type Nodes](#examples-on-primitive-type-nodes)
- [Comparison with Current PyTA Implementation](#comparison-with-current-pyta-implementation)
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

## Comparison with Current PyTA Implementation

My first intuition was to compare the default end location attributes with those produced by the transformer.
Specifically, I modified `set_endings_from_source` in the factory function `end_setter_from_source` to simply return the
same node without mutation.

**Note**: These changes were temporary and only intended to test the end location attributes.

```python
def end_setter_from_source(source_code, pred, only_consumables=False):
    """Returns a *function* that sets ending locations for a node from source.

    The basic technique is to do the following:
      1. Find the ending locations for the node based on its last child.
      2. Starting at that point, iterate through characters in the source code
         up to and including the first index that satisfies pred.

    pred is a function that takes a string and index and returns a bool,
    e.g. _is_close_paren

    If only_consumables is True, the search halts when it reaches a non-consumable
    character that fails pred *on the first line*.
    TODO: really the behaviour should be the same for all lines searched for.
    """

    def set_endings_from_source(node):
        return node
    return set_endings_from_source
```

This resulted in 49 out of 58 tests passing.

**Reminder**: each tuple in the lists correspond to `(node.fromlineno, node.end_lineno, node.col_offset, node.end_col_offset)`.

Skip to [observations](###-observations) of failed tests.

### 1) Fail: test_await (Await node)

Expected :[(5, 5, 4, 27)] \
Actual :[(5, 5, 4, 25)]

### 2) Fail: test_call (Call node)

Expected :[(1, 2, 0, 9)] \
Actual :[(1, 2, 0, 6)]

### 3) Fail: test_comprehension (Comprehension node)

Expected :[(1, 1, 7, 20), (2, 2, 7, 16), (2, 2, 21, 36), (3, 3, 9, 18), (3, 3, 23, 40)] \
Actual :[(1, 1, 7, 19), (2, 2, 7, 16), (2, 2, 21, 35), (3, 3, 9, 18), (3, 3, 23, 39)]

### 4) Fail: test_decorators (decorators node)

Expected :[(1, 2, 0, 27), (6, 6, 0, 9)] \
Actual :[(1, 2, 0, 24), (6, 6, 0, 9)]

### 5) Fail: test_generatorexp (GeneratorExp node)

Expected :[(1, 1, 0, 37), (2, 2, 0, 43)] \
Actual :[(1, 1, 0, 35), (2, 2, 0, 39)]

### 6) Fail: test_list (List node)

Expected :[(1, 1, 0, 2), (2, 2, 0, 9), (3, 3, 0, 6), (4, 9, 0, 1)] \
Actual :[(1, 1, 0, 2), (2, 2, 0, 8), (3, 3, 0, 5), (4, 8, 0, 5)]

### 7) Fail: test_raise (Raise node)

Expected :[(3, 3, 8, 24), (5, 5, 8, 36)] \
Actual :[(3, 3, 8, 24), (5, 5, 8, 35)]

### 8) Fail: test_tuple (Tuple node)

Out of all Tuple nodes in the example file, the 18-th node's end location was wrong:

Expected: (21, 21, 0, 2) \
Actual: (1, 1, 0, 6)

### 9) Fail: test_yieldfrom (YieldFrom node)

Expected :[(2, 2, 4, 23)] \
Actual :[(2, 2, 4, 22)]

### Observations

From the failed tests, we can make a key observation: both `end_lineno` and `end_col_offset` are not always accurate.
The `end_lineno` attribute was inaccurate only in `test_list`, while `end_col_offset` was inaccurate in every failed test.

It is clear that the current astroid logic for computing end locations is not fully reliable. In particular, it often fails
in cases involving whitespace. For example, in test_call:

```python
print(1, 2, 3,
     4  )
```

Astroid computed `end_col_offset` as 6, when in reality it should be 9. This issue is frequent enough to matter,
especially considering the fact that the current PyTA implementation passes all tests.

> This gets a bit complicated because we implemented some interesting string parsing to capture the full extent (start and end locations) of some nodes, because we didn't think astroid did it correctly.

Your intuition was correct: astroid does not consistently evaluate node end locations accurately.

## Conclusion

From this investigation, we can conclude that while astroid is usually correct for simpler nodes (such as primitive types),
it struggles to accurately determine the end locations of more complex nodes. This inaccuracy is significant because
PyTA’s current logic already works and passes all tests.

Therefore, it would be best to continue using PyTA’s custom logic rather than relying on astroid’s defaults.
