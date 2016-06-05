from astroid.scoped_nodes import FunctionDef
from astroid.scoped_nodes import ClassDef
from astroid.manager import AstroidManager


class DocumentedModule:
    '''Encapsulates a module with all the classes and top level functions being
    documented.'''

    def __init__(self, module_path):
        '''Takes a Python file located at module_path, reads the AST and
        generates the appropriate documentation objects.
        '''
        ast = AstroidManager().ast_from_file(module_path)
        body = ast.body
        self.functions = []
        self.classes = []
        for node in body:
            if isinstance(node, FunctionDef):
                self.functions.append(DocumentedFunction(node))
            elif isinstance(node, ClassDef):
                self.classes.append(DocumentedClass(node))


class DocumentedFunction:
    '''Encapsulates a function. This can be used for methods as well.'''
    
    def __init__(self, node):
        '''Takes the Astroid node and extracts the data. It should be a
        FunctionDef node.
        '''
        self.name = node.name
        self.args = [x.name for x in node.args.args] if node.args else []
        self.docstring = node.doc if node.doc else ''


class DocumentedClass:
    '''Encapsulates a class with the documentation and documented methods.'''
    
    def __init__(self, node):
        '''Takes the Astroid node and extracts the data. It should be a
        ClassDef node.
        '''
        self.docstring = node.doc if node.doc else ''
        self.name = node.name
        self.methods = []
        for n in node.body:
            if isinstance(n, FunctionDef):
                self.methods.append(DocumentedFunction(n))
