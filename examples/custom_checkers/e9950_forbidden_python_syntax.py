"""Examples for E9950 forbidden-python-syntax."""

count = 10
while count > -1:  # forbidden python syntax
    if count == 5:
        continue  # forbidden python syntax

for i in range(1, 10):  # forbidden python syntax
    if i == 5:
        break  # forbidden python syntax

squares = [i ** 2 for i in range(1, 10)]  # forbidden python syntax
