class Example(object):
    def field(self, num):
        return num
    def __init__(self):
        self.field = 'Masking the function with this string'

# If you call Example().field(num), it will error out since we masked it
