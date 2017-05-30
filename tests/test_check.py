"""Run from the `pyta` root directory to use the local `python_ta` rather than 
installed `python_ta` package.
"""
import os
import sys
import python_ta

def test_check_on_dir():
    """The function, check_all() should handle a top-level dir as input."""
    _inputs = [
        ['nodes'],
        ['examples']
    ]
    for item in _inputs:
        python_ta.check_all(item)

def test_check_on_file():
    """Test files"""
    _inputs = [
        ['nodes/Name.py'],
        ['nodes/Dict.py', 'nodes.Const.py']
    ]
    for item in _inputs:
        python_ta.check_all(item)

def test_check_on_bad_input():
    """Test bad inputs. In all cases, pyta should recover. 
    Any valid files, if any, should be checked.
    """
    _inputs = [
        [222],
        222,
        ['nodes/Dict.py nodes/Const.py'],
        [222, 'examples/inline_config_comment.py', 'nodes/Dict.py'],
        ['file_does_not_exist']
    ]
    for item in _inputs:
        python_ta.check_all(item)

def test_check_with_config():
    """Test inputs along with a config arg."""
    _inputs = [
        ['nodes/Const.py'],
        ['nodes']
    ]
    CONFIG = {
        # [ELIF]
        'max-nested-blocks': 4,
        # [FORMAT]
        'max-line-length': 80,
        # [FORBIDDEN IMPORT]
        'allowed-import-modules': ['doctest', 'unittest', 'hypothesis', 
                                   'python_ta'],
        # [FORBIDDEN IO]
        'allowed-io': [],
        # [MESSAGES CONTROL]
        'disable': ['R0401', 'R0901', 'R0903', 'R0904', 'R0911', 'R0916', 
                    'W0402', 'W0403', 'W0410', 'W1501', 'W1502', 'W1505',
                    'E1300', 'E1301',  'E1302', 'E1304', 'W1300', 'W1301',
                    'W1302', 'W1304', 'E1124',  'E1125', 'E1129', 'E1132',
                    'W1402', 'W0105', 'E1303', 'W1306',  'W1307', 'E0116',
                    'E0114', 'E0112', 'E0115', 'E0106', 'E0113',  'E0111',
                    'E0105', 'E0100', 'E0117', 'W0150', 'W0120', 'W0124',
                    'W0108', 'W0123', 'W0122', 'W0110', 'C0122', 'C0200',
                    'W0141', 'W0640', 'W0623', 'W0614', 'W0604', 'W0603',
                    'W0602', 'W0601',  'E0604', 'E0603', 'E1200', 'E1201',
                    'E1202', 'W1201', 'E1205',  'E1206', 'similarities',
                    'newstyle', 'python3', 'W0512',  'C0403', 'C0401',
                    'C0402', 'E1701', 'E1700', 'W0332', 'C0327',  'C0328',
                    'E0202', 'E0241', 'E0704', 'W0211', 'W0232', 'W0511',
                    'R0204', 'C0303', 'W0231']
    }
    for item in _inputs:
        python_ta.check_all(item, config=CONFIG)
