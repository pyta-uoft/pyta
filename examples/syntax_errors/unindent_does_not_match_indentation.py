num_even = 0
num_odd = 0
for i in range(100):
    if i % 2 == 0:
        num_even += 1
      else:  # Error on this line: six spaces before `else:` instead of four
        num_odd += 1
