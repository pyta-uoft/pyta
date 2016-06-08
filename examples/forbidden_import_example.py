import re
__import__(re)


def greet(name):
    """Print a message to the user."""
    if re.search('[a-zA-Z]{5}', name) is None:
        print('Invalid name')
    else:
        print('hello, ' + name)


if __name__ == '__main__':
    greet('david')

