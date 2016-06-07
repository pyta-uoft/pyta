class MyClass:
	def __init__(self):
		pass
	
	def methodA(not_self):  # Bad (should be 'self')
		pass

	def methodB(self):  # Good
		pass
