import cProfile
import io
import os
import pstats
import subprocess
import sys
import time


def profile_test_examples(n_runs=3, verbose=False, test_filter=None):
    """
    Profile the test_examples.py test suite execution.

    Args:
        n_runs: Number of times to run the tests for averaging
        verbose: Whether to print detailed profiling stats
        test_filter: Optional test filter (e.g., 'test_examples_files_pyta', 'test_pycodestyle_errors_pyta')

    Returns:
        dict with timing and profiling statistics
    """
    total_time = 0.0
    total_calls = 0
    times = []

    test_path = "tests/test_examples.py"
    if test_filter:
        test_path = f"{test_path}::{test_filter}"

    print(f"\n{'='*70}")
    print(f"Profiling test_examples.py")
    print(f"Test filter: {test_filter if test_filter else 'ALL TESTS'}")
    print(f"Number of runs: {n_runs}")
    print(f"{'='*70}\n")

    for i in range(n_runs):
        profile_file = f"test_examples_profile_{i}.prof"

        # Profile pytest execution
        start = time.perf_counter()
        result = subprocess.run(
            [
                "python3",
                "-m",
                "cProfile",
                "-o",
                profile_file,
                "-m",
                "pytest",
                test_path,
                "-v" if verbose else "-q",
                "--tb=short",
            ],
            capture_output=True,
            text=True,
        )
        end = time.perf_counter()

        duration = end - start
        times.append(duration)
        total_time += duration

        # Read profiling stats
        stats = pstats.Stats(profile_file)
        total_calls += stats.total_calls

        print(f"--- Run {i + 1}/{n_runs} ---")
        print(f"  Wall time: {duration:.4f} seconds")
        print(f"  Total function calls: {stats.total_calls:,}")

        if verbose and i == 0:  # Only print detailed stats on first run
            # Print top 30 time-consuming functions
            s = io.StringIO()
            ps = pstats.Stats(profile_file, stream=s)
            ps.strip_dirs().sort_stats("cumulative")

            print(f"\n  Top 30 functions by cumulative time:")
            ps.print_stats(30)

            print(f"\n  Top 30 functions by total time:")
            ps.sort_stats("tottime").print_stats(30)

        # Clean up profile file
        os.remove(profile_file)

    avg_time = total_time / n_runs
    avg_calls = total_calls // n_runs
    min_time = min(times)
    max_time = max(times)
    std_dev = (sum((t - avg_time) ** 2 for t in times) / n_runs) ** 0.5

    print(f"\n{'='*70}")
    print(f"SUMMARY - test_examples.py Profiling Results")
    print(f"{'='*70}")
    print(f"  Average time:           {avg_time:.4f} seconds")
    print(f"  Min time:               {min_time:.4f} seconds")
    print(f"  Max time:               {max_time:.4f} seconds")
    print(f"  Std deviation:          {std_dev:.4f} seconds")
    print(f"  Average function calls: {avg_calls:,}")
    print(f"{'='*70}\n")

    return {
        "average_time": avg_time,
        "min_time": min_time,
        "max_time": max_time,
        "std_dev": std_dev,
        "times": times,
        "average_calls": avg_calls,
    }


def time_examples_files_pyta(n_runs=5):
    """
    Time the execution of test_examples_files_pyta specifically (without cProfile overhead).
    This gives a cleaner measurement of just the test execution time.

    Args:
        n_runs: Number of times to run the test for averaging

    Returns:
        dict with timing statistics
    """
    print(f"\n{'='*70}")
    print(f"Timing test_examples_files_pyta")
    print(f"Number of runs: {n_runs}")
    print(f"{'='*70}\n")

    times = []

    for i in range(n_runs):
        start = time.perf_counter()
        result = subprocess.run(
            [
                "python3",
                "-m",
                "pytest",
                "tests/test_examples.py::test_examples_files_pyta",
                "-q",
                "--tb=no",
            ],
            capture_output=True,
            text=True,
        )
        end = time.perf_counter()

        duration = end - start
        times.append(duration)

        print(f"--- Run {i + 1}/{n_runs} ---")
        print(f"  Time: {duration:.4f} seconds")

        # Show pass/fail status
        if result.returncode == 0:
            print(f"  Status: ✓ PASSED")
        else:
            print(f"  Status: ✗ FAILED (return code: {result.returncode})")

    avg_time = sum(times) / len(times)
    min_time = min(times)
    max_time = max(times)
    std_dev = (sum((t - avg_time) ** 2 for t in times) / n_runs) ** 0.5

    print(f"\n{'='*70}")
    print(f"SUMMARY - test_examples_files_pyta Timing")
    print(f"{'='*70}")
    print(f"  Average time:  {avg_time:.4f} seconds")
    print(f"  Min time:      {min_time:.4f} seconds")
    print(f"  Max time:      {max_time:.4f} seconds")
    print(f"  Std deviation: {std_dev:.4f} seconds")
    print(f"  Range:         {max_time - min_time:.4f} seconds")
    print(f"{'='*70}\n")

    return {
        "average_time": avg_time,
        "min_time": min_time,
        "max_time": max_time,
        "std_dev": std_dev,
        "times": times,
    }


def compare_test_methods(n_runs=2):
    """
    Compare execution time of different test methods in test_examples.py.
    """
    test_methods = [
        "test_examples_files_pyta",
        "test_pycodestyle_errors_pyta",
        "test_c9104_module_name_violation",
        "test_cyclic_import",
    ]

    print(f"\n{'='*70}")
    print(f"Comparing Test Methods in test_examples.py")
    print(f"Runs per test: {n_runs}")
    print(f"{'='*70}\n")

    results = {}

    for test_name in test_methods:
        times = []

        for i in range(n_runs):
            start = time.perf_counter()
            result = subprocess.run(
                [
                    "python3",
                    "-m",
                    "pytest",
                    f"tests/test_examples.py::{test_name}",
                    "-q",
                    "--tb=no",
                ],
                capture_output=True,
                text=True,
            )
            end = time.perf_counter()

            times.append(end - start)

        avg_time = sum(times) / len(times)
        results[test_name] = {"avg_time": avg_time, "times": times}

        print(f"{test_name:45s}: {avg_time:8.4f}s (min: {min(times):.4f}s, max: {max(times):.4f}s)")

    print(f"\n{'='*70}")
    print(f"Test Methods Sorted by Average Time (slowest first):")
    print(f"{'='*70}\n")

    sorted_results = sorted(results.items(), key=lambda x: x[1]["avg_time"], reverse=True)
    for i, (test_name, data) in enumerate(sorted_results, 1):
        print(f"{i}. {test_name:45s}: {data['avg_time']:.4f}s")

    print(f"\n{'='*70}\n")

    return results


if __name__ == "__main__":
    # Usage examples:
    # python profile_test_examples.py compare
    # python profile_test_examples.py compare 5
    # python profile_test_examples.py time-pyta
    # python profile_test_examples.py time-pyta 5

    if len(sys.argv) > 1:
        command = sys.argv[1].lower()

        if command == "compare":
            # Compare different test methods
            n_runs = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 2
            compare_test_methods(n_runs=n_runs)

        elif command == "time-pyta":
            # Time test_examples_files_pyta specifically
            n_runs = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 5
            time_examples_files_pyta(n_runs=n_runs)

        else:
            print(f"Unknown command: {command}")
            sys.exit(1)
    else:
        sys.exit(1)
