"""
Simple Tree class to be used for RecursionTable
"""


class Tree:
    def __init__(self, value):
        self.value = value
        self.children = []

    def add_child(self, child_node):
        self.children.append(child_node)

    def check_tree_equality(self, tree1):
        if self.value != tree1.value or len(self.children) != len(tree1.children):
            return False
        for i in range(len(self.children)):
            if not self.children[i].check_tree_equality(tree1.children[i]):
                return False
        return True
