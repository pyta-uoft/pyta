"""Example showing a forbidden execution of eval()."""


def dynamic_execution(name):
    eval('hello, my name is ' + name)

if __name__ == '__main__':
    dynamic_execution('hayley')

