"""
ClassDef astroid node

A class definition.

Attributes:
    - basenames             (list[str])
        - The names of the parent classes. Names are given in the order they appear in the
        class definition.
    - bases                 (list[NodeNG])
        - List of nodes for explicitly specified base classes.
    - body                  (list[NodeNG])
        - The contents of the class body.
    - decorators            (Optional[Decorators])
        - The decorator to be applied on this function.
    - doc                   (Optional[str])
        - The docstring of this function.
    - keywords               (Optional[list[Keyword]])
        - The keywords given to the class definition.
    - name                  (str)
        - A raw string for the class name.
    - newstyle              (Optional[bool])
        - Whether this is a "new style" class or not.
    - special_attributes    (objectmodel.ClassModel)
        - The names of special attributes that this class has.
    - type                  (str)
        - The class type for this node. Possible values: "class", "metaclass", and "exception".

Example:
    ClassDef(
        name='Foo',
        doc=None,
        decorators=Decorators(nodes=[Name(name='wrapper')]),
        bases=[
            Name(name='base1'),
            Name(name='base2')],
        keywords=[],
        body=[Pass()])

Type-checking:
    The class name is added to the parent's type environment.
    The class' instance variables and methods are used to update the global TypeStore.
"""

@wrapper
class Foo(base1, base2):
    pass
