class ClassWithNoInit:
    def does_stuff(self, n):
        return n
    def does_more_stuff(self, n, m):
        return n * m


class ClassWithNoInitTwo(ClassWithNoInit):
    def does_nothing(self):
        print('hello')
