class C:
	def __init__(self):
		self.num = 5
	
	@staticmethod
	def method(self):  # Static methods do not have a 'self'
		self.num += 1
