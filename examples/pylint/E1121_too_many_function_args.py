"""pylint: too many function args.
"""


class User:
    def __init__(self, name, age):
        """
        Initialize the User.

        @type self: User
        @type name: str
        @type age: int
        @rtype: None
        """
        self.name = name
        self.age = age

User("David", 21, 4)
