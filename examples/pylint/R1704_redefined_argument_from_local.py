def greet_person(name, friends) -> None:
    """Print the name of a person and all their friends."""
    print("My name is {}".format(name))
    for name in friends:  # Error on this line
        print("I am friends with {}".format(name))
