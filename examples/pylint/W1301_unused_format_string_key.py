my_dict = {
    'a': 1,
    'b': 2
}
print('Format string {a} {c}'.format(**my_dict))  # Error on this line: key 'c' not found in dict
