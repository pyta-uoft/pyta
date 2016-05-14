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


class TestExamples(unittest.TestCase):
	def testExamples(self):
		global _EXAMPLE_PREFIX_REGEX
		success = True  # Success is only true if all tests pass.
		for test_file in get_test_file_paths():
			passes = False  # This determines if the test fails.
			base_name = os.path.basename(test_file)  # Gets the name of the file.
			if not re.match(_EXAMPLE_PREFIX_REGEX, base_name[:5]):
				raise Exception('Invalid file prefix: ' + base_name)
			checker_name = base_name[6:-3].replace('_', '-')  # Extracts the Ldddd_ and .py
			output = subprocess.run(['pylint', '--reports=n', test_file], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
			for line in output.stdout.decode('utf-8').split('\n'):
				if checker_name in line:
					passes = True
					break
			if not passes:
				print('Unable to find error in', base_name)
				success = False
		self.assertTrue(success)


if __name__ == '__main__':
	unittest.main()
