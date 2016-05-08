"""pylint: format needs mapping
"""
gpl = "%(id)s : %(atr)s"

objects = [{'id': 1, 'content': [{'atr': 'big', 'no': 2}]},
           {'id': 2, 'content': [{'atr': 'small', 'no': 3}]}]

for obj in objects:
    for con in obj['content']:
        print(gpl % (obj, con))    # Error on this line
