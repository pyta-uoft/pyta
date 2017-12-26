from setuptools import setup


def readme():
    try:
        import pypandoc
    except ImportError:
        return ''

    return pypandoc.convert('README.md', 'rst')

setup(
    name='python-ta',
    version='1.3.0',
    description='Code checking tool for teaching Python',
    long_description=readme(),
    url='http://github.com/pyta-uoft/pyta',
    author='David Liu',
    author_email='david@cs.toronto.edu',
    license='MIT',
    packages=['python_ta', 'python_ta.reporters', 'python_ta.checkers',
              'python_ta.docstring', 'python_ta.patches', 'python_ta.parser',
              'python_ta.transforms', 'python_ta.typecheck'],
    install_requires=[
        'astroid>=1.6',
        'funcparserlib',
        'hypothesis',
        'pycodestyle',
        'pylint>=1.8',
        'nose',
        'colorama',
        'six',
        'jinja2',
        'pygments'
    ],
    include_package_data=True,
    zip_safe=False)
