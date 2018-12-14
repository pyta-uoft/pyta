from setuptools import setup


def readme():
    try:
        import pypandoc
    except ImportError:
        return ''

    return pypandoc.convert('README.md', 'rst')

setup(
    name='python-ta',
    version='1.4.2',
    description='Code checking tool for teaching Python',
    long_description=readme(),
    url='http://github.com/pyta-uoft/pyta',
    author='David Liu',
    author_email='david@cs.toronto.edu',
    license='MIT',
    packages=['python_ta', 'python_ta.reporters', 'python_ta.checkers',
              'python_ta.docstring', 'python_ta.patches', 'python_ta.parser',
              'python_ta.transforms', 'python_ta.typecheck', 'python_ta.util'],
    install_requires=[
        'astroid>=2.0,<2.1',
        'funcparserlib',
        'hypothesis',
        'pycodestyle',
        'pylint>=2.1,<2.2',
        'nose',
        'colorama',
        'six',
        'jinja2',
        'pygments'
    ],
    extras_require={
        'dev': [
            'graphviz'
        ]
    },
    python_requires='~=3.7',
    include_package_data=True,
    zip_safe=False)
