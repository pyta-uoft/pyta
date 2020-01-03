from setuptools import setup


with open('README.md') as fh:
    long_description = fh.read()

setup(
    name='python-ta',
    version='1.5.0',
    description='Code checking tool for teaching Python',
    long_description=long_description,
    long_description_content_type='text/markdown',
    url='http://github.com/pyta-uoft/pyta',
    author='David Liu',
    author_email='david@cs.toronto.edu',
    license='MIT',
    packages=['python_ta', 'python_ta.reporters', 'python_ta.checkers',
              'python_ta.cfg', 'python_ta.contracts',
              'python_ta.docstring', 'python_ta.patches', 'python_ta.parser',
              'python_ta.transforms', 'python_ta.typecheck', 'python_ta.util'],
    install_requires=[
        'astroid>=2.3,<2.4',
        'funcparserlib',
        'hypothesis',
        'pycodestyle',
        'pylint>=2.4,<2.5',
        'colorama',
        'six',
        'jinja2',
        'pygments',
        'wrapt'
    ],
    extras_require={
        'dev': [
            'coveralls',
            'graphviz',
            'pytest',
            'pytest-cov'
        ]
    },
    python_requires='~=3.8',
    include_package_data=True,
    zip_safe=False)
