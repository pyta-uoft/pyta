from astroid.scoped_nodes import FunctionDef
from astroid.scoped_nodes import ClassDef
from astroid.manager import AstroidManager


class DocumentedModule:
    """Encapsulates a module with all the classes and top level functions being
    documented. When provided a module, it will use astroid to traverse all the
    nodes, and create all the DocumentedMethods and DocumentedFunctions, which
    can be accessed through their respective fields."""

    def __init__(self, module_path):
        """Takes a Python file located at module_path, reads the AST and
        generates the appropriate documentation objects.
        module_path: Must be a valid path that can be read from, which is the
        desired module to read.
        """
        ast = AstroidManager().ast_from_file(module_path)
        body = ast.body
        self.functions = self._read_top_level_functions_from_ast_body(body)
        self.classes = self._read_classes_from_ast_body(body)

    def _read_top_level_functions_from_ast_body(self, body):
        """Takes the top level node (the body node from Astroid) and reads
        all of the top level functions. Upon reading their data to create
        a list of DocumentedFunctions, the list is returned.
        """
        documented_funcs = []
        for node in body:
            if isinstance(node, FunctionDef):
                documented_funcs.append(DocumentedFunction(node))
        return documented_funcs

    def _read_classes_from_ast_body(self, body):
        """Takes the top level node (the body node from Astroid) and reads
        all of the classes. Upon extracting their data to create a list of
        DocumentedClasses, the list is returned.
        """
        documented_classes = []
        for node in body:
            if isinstance(node, ClassDef):
                documented_classes.append(DocumentedClass(node))
        return documented_classes


class DocumentedFunction:
    """Encapsulates a function with the documentation and a list of arguments.
    This can be used for class methods as well. If there are no arguments or
    docstrings, they will be their empty values (for args this is an empty
    list, and for the docstring this is an empty string).
    """
    
    def __init__(self, node):
        """Takes the Astroid node and extracts the data. It should be a
        FunctionDef node.
        """
        self.name = node.name
        self.args = [x.name for x in node.args.args] if node.args else []
        self.docstring = node.doc if node.doc else ''


class DocumentedClass:
    """Encapsulates a class with the documentation and documented methods.
    The docstring for the class is also available, along with a list of all
    the DocumentedFunctions, which are the methods of this class that have
    been documented.
    Note that docstrings will never be None, but rather just an empty string
    if no documentation exists."""
    
    def __init__(self, node):
        """Takes the Astroid node and extracts the data. It should be a
        ClassDef node. All of the methods are DocumentedFunctions.
        """
        self.docstring = node.doc if node.doc else ''
        self.name = node.name
        self.methods = []
        for n in node.body:
            if isinstance(n, FunctionDef):
                self.methods.append(DocumentedFunction(n))
