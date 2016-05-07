"""pylint: too many nested blocks

Note: we set a limit of three nested if blocks.
"""

def my_f(num):
    if num > 0:
        if num > 3:
            if num > 10:
                if num < 50:
                    print(num)
    else:
        print('done')
