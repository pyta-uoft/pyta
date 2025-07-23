"""
This Python module is designed for testing the snapshot function's ability to return
variables from the __main__ stack frame, particularly globally defined variables.

This module is intended exclusively for testing purposes and should not be used for any other purpose.
"""

from __future__ import (
    annotations,  # "annotations" should not be included in the snapshot
)

import json

from python_ta.debug.id_tracker import IDTracker
from python_ta.debug.snapshot import snapshot

# globally defined variables
team_lead = "David Liu"
SDS_projects = ["PyTA", "MarkUs", "Memory Models"]
team_num = 9

print(json.dumps(snapshot(IDTracker())[0]))
