class Foo:
    pass


class Bar(Foo):
    def __init__(self):
        super(Foo, self).__init__()  # Error on this line
