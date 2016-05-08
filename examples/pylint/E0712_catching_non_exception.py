class RandomClass:
	pass

def throw_exception():
	try:
		n = 5 / 0  # Will throw a ZeroDivisionError
	except RandomClass:
		print('The above does not inherit from BaseException')
	except ZeroDivisionError:
		print('Will not be reached due to erroring out earlier')
