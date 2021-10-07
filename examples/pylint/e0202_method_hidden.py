class Person:
    """Generic person with a name and a hobby."""
    name: str
    hobby: str

    def __init__(self, name: str, hobby: str) -> None:
        self.name = name
        self.hobby = hobby

    def hobby(self) -> str:  # Error on this line
        return "No hobbies; I just work and study!"
