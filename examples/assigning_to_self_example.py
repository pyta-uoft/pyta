class Assigning():
    def __init__(self, value, name):
        self.value = value
        self.name = name
        
    def new(self, newvalue, newname):
        # wrong approach
        self = newvalue  # Error on this line
        # correct approach
        self.name = newname
