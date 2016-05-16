import unittest
import os
import os.path
import subprocess
import re


_EXAMPLES_PATH = '../examples/pylint/'
_EXAMPLE_PREFIX_REGEX = '[CEFRW]\d{4}'


def get_test_file_paths():
	"""Gets all the files from the examples folder for testing."""
	# Since examples are located elsewhere, change there first. 
	old_wd = os.getcwd()
	os.chdir(_EXAMPLES_PATH)
	cur_wd = os.getcwd()
	# Now get every file.
	test_files = []
	for test_file in os.listdir('.'):
		path = os.path.join(cur_wd, test_file)
		if os.path.isfile(path):
			test_files.append(path)
	# Restore back to our old current working directory before returning.
	os.chdir(old_wd)
	return test_files


def create_test_function(test_file, checker_name):
	"""Creates a test function from a test file, and a checker name.
	test_file: The full path (string) to the file.
	checker_name: The hyphenated checker name that should be detected.
	An example of a valid checker_name would be: 'no-init-classes'
	"""
	# The following are captured when this function is created.
	def new_test_func(self):
		found_pylint_message = False
		output = subprocess.run(['pylint', '--reports=n', test_file], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
		for line in output.stdout.decode('utf-8').split('\n'):
			if checker_name in line:
				found_pylint_message = True
				break
		self.assertTrue(found_pylint_message)
	return new_test_func


def make_new_unit_tests():
	"""Creates all the new unit tests dynamically."""
	global _EXAMPLE_PREFIX_REGEX
	for test_file in get_test_file_paths():
		base_name = os.path.basename(test_file)
		if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
			raise Exception('Invalid file prefix: %s' % base_name)
		if not base_name.lower().endswith('.py'):
			raise Exception('Not a python file: %s' % base_name)
		checker_name = base_name[6:-3].replace('_', '-')  # Take off prefix and file extension.
		test_function = create_test_function(test_file, checker_name)
		setattr(TestExamples, 'test_%s' % base_name, test_function)


class TestExamples(unittest.TestCase):
	"""The test class to be populated dynamically."""
	pass


if __name__ == '__main__':
	make_new_unit_tests()
	unittest.main()
