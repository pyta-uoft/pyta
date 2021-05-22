err = "my error"
try:
    print(x)
except NameError as err:  # Error on this line: handler assigns exception to an existing name
    print('Exception occurred')
