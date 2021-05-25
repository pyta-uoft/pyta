# mapping = {'hi': 1, 'hello': 2} # maybe this?  # Error on this line: non-mapping value used in a mapping context

def square(n):
    return n * n


result = map(square, 'test')
print(result)

if __name__ == '__main__':
    import python_ta
    python_ta.check_all(config={
        'max-line-length': 100
    })
