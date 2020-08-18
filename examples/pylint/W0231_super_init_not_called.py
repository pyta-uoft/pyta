class Base:
    def __init__(self):
        print('Base init')

class Derived(Base):
    def __init__(self):
        print('Derived init') # Error on this line [no call to Base.__init__()]
