"""
Utility class for running the Black formatting tool.
"""

import subprocess
import sys
from typing import Optional


class Autoformatter:
    """
    A class for running the Black formatting tool.

    Instance attributes:
        - subprocess_args: a list of command-line arguments to be passed into Black
    """

    subprocess_args: list[str]

    def __init__(self, autoformat_options: list[str], max_linelen: Optional[int]):
        """
        Initialize an autoformatter with the given autoformat options and maximum line length.
        """
        self.subprocess_args = [sys.executable, "-m", "black"]
        if max_linelen:
            self.subprocess_args.append("--line-length=" + str(max_linelen))
        for arg in autoformat_options:
            self.subprocess_args.append("--" + arg)

    def run(self, file_path: str):
        """
        Run the Black formatting tool on the given Python file.
        """
        subprocess.run(
            self.subprocess_args + [file_path],
            encoding="utf-8",
            capture_output=True,
            text=True,
            check=True,
        )
