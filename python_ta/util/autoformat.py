"""
This file contains a function for running the Black formatting tool.
"""

import subprocess
import sys


def run_autoformat(file_path: str, autoformat_options: list[str], max_linelen: int) -> None:
    """Run the Black formatting tool on the Python file with the given autoformat options and maximum line length."""
    subprocess_args = [sys.executable, "-m", "black"]
    if max_linelen:
        subprocess_args.append(f"--line-length={max_linelen}")
    for arg in autoformat_options:
        subprocess_args.append("--" + arg)

    subprocess.run(
        subprocess_args + [file_path],
        encoding="utf-8",
        capture_output=True,
        text=True,
        check=True,
    )
