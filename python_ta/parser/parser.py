import re

token_type={
	'keyword'     : 0,
	'identifier'  : 1,
	'integer'     : 2,
	'operator'    : 3,
	'indent'      : 4,
	'dedent'      : 5,
	'newline'     : 6,
	'endmarker'   : 7,
	'delimiter'   : 8,
}

token_type_string=[
	'keyword',
	'identifier',
	'integer',
	'operator',
	'indent',
	'dedent',
	'newline',
	'endmarker',
	'delimiter',
]

keyword = set([
	'def',
	'return',
	'and',
])

class token:
	def __init__(self, type, value=None):
		self.type=token_type[type]
		self.value=value

	def getType(self):
		return self.type

	def getValue(self):
		return self.value

	def __str__(self):
		return ((token_type_string[self.type]+': '+str(self.value)) 
			if self.value else token_type_string[self.type])

def lexer(str):
	temp=filter(None,re.split(r"( |\(|\)|\n(?: |\t)*|:|\+|\-|\*|\\|,)", str))
	temp_0=[]
	indent=0
	for i in temp:
		if i[0]=='\n':
			if len(i)-1>indent:
				temp_0.append(token('indent'))
				indent=len(i)-1
			elif len(i)-1<indent:
				temp_0.append(token('dedent'))
				indent=len(i)-1
			else:
				temp_0.append(token('newline'))
		elif i==' ':
			pass
		elif re.match(r"^\d+$", i):
			temp_0.append(token('integer', int(i)))
		elif re.match(r"^(\d+.\d*|\d*.\d+)$", i):
			temp_0.append(token('float', float(i)))
		elif re.match(r"^\w+$", i):
			if i in keyword:
				temp_0.append(token('keyword', i))
			else:
				temp_0.append(token('identifier', i))
		elif re.match(r"^(\+|\-|\*|\\)$", i):
			temp_0.append(token('operator', i))
		elif re.match(r"^(\(|\)|:|,)$", i):
			temp_0.append(token('delimiter', i))
	if indent>0:
		temp_0.append(token('dedent'))
	temp_0.append(token('endmarker'))
	return temp_0

def parser(tokens):
	def funcdef(tokens, index):
		if tokens[index].getType()==token_type['keyword'] and tokens[index].getValue()=='def':
			index=index+1
			if tokens[index].getType()==token_type['identifier']:
				func_name=tokens[index].getValue()
				index=index+1
				ret=parameters(tokens, index)
				args=ret[0]
				index=ret[1]
				if tokens[index].getType()==token_type['delimiter']  and tokens[index].getValue()==':':
					index=index+1
					ret=suite(tokens, index)
					body=ret[0]
					index=ret[1]
					return [['def',func_name,args,body], index]
				else:
					raise(Exception("Syntax Error: expect a symbol ':', given: "+str(tokens[index].getValue())))
			else:
				raise(Exception("Syntax Error: expect an identifier as function name, given: "+str(tokens[index].getValue())))
		else:
			raise(Exception("Syntax Error: expect the keyword def"))

	def parameters(tokens, index):
		if tokens[index].getType()==token_type['delimiter'] and tokens[index].getValue()=='(':
			index=index+1
			argslist=[]
			if tokens[index].getType()==token_type['identifier']:
				ret=typedargslist(tokens, index)
				argslist=ret[0]
				index=ret[1]
			if tokens[index].getType()==token_type['delimiter'] and tokens[index].getValue()==')':
				index=index+1
				return [['args',argslist], index]
			else:
				raise(Exception("Syntax Error: expect a closed parentheses ')', given: "+str(tokens[index].getValue())))
		else:
			raise(Exception("Syntax Error: expect a parentheses '(', given: "+str(tokens[index].getValue())))

	def typedargslist(tokens, index):
		if tokens[index].getType()==token_type['identifier']:
			argslist=[]
			argslist.append(tokens[index].getValue())
			index=index+1
			while tokens[index].getType()==token_type['delimiter'] and tokens[index].getValue()==',':
				index=index+1
				if tokens[index].getType()==token_type['identifier']:
					argslist.append(tokens[index].getValue())
					index=index+1
				else:
					raise(Exception("Syntax Error: expect an identifier as parameter name, given: "+str(tokens[index].getValue())))
			return [argslist, index]
		else:
			raise(Exception("Syntax Error: expect an identifier as parameter name, given: "+str(tokens[index].getValue())))

	def suite(tokens, index):
		return [[],index]

	return funcdef(tokens, 0)[0]

code = """def f(x,y,z):"""

print(parser(lexer(code)))