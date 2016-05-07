def func(num):
	try:
		result = num / 0
	except Exception:
		print('This is always triggered')
	except ZeroDivisionError:
		print('Cannot ever be reached')
