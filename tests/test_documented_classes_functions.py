from comment_extractor import *
import unittest


class TestDocumentations(unittest.TestCase):
    def setUp(self):
        self.dm = DocumentedModule('resources/random_file.py')

    def test_classes(self):
        c = self.dm.classes[0]
        method = c.methods[0]
        self.assertEqual(c.name, 'MyTestClass')
        self.assertEqual(c.docstring, 'Some documentation')
        self.assertEqual(method.name, '__init__')
        self.assertEqual(method.args, ['self', 'a'])
        self.assertEqual(method.docstring, 'Init docs')

    def test_functions(self):
        func = self.dm.functions[0]
        self.assertEqual(func.name, 'top_level_func')
        self.assertEqual(func.args, [])
        self.assertEqual(func.docstring, 'A top level function')


if __name__ == '__main__':
    unittest.main()
