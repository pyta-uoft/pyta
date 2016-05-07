class RandomClass:
	pass


def throw_exception():
	try
		n = 5 / 0
	except RandomClass:
		print('The above does not inherit from BaseException')
