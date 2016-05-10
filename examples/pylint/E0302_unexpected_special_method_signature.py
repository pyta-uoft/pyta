class A:
	def __init__(self):
		pass
	def __str__(self):  # Good, this is what is expected
		return 'string'
		
class B:
	def __init__(self):
		pass
	def __str__(self, a):  # Bad, Python won't know what to put in 'a'
		return 'string'
