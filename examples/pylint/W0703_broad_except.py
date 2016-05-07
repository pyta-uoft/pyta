def something_dangerous():
	pass

def too_generic():
	try:
		something_dangerous()
	except:
		print('Should specify a reasonable exception type')
