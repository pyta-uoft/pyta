class CustomException(Exception):
	pass

def bad_raise():
	# Bad example, needs to be in an 'except' block:
	raise
	
	# How to properly use:
	try:
		raise CustomException
	except CustomException:
		raise  # Continue passing on the error
