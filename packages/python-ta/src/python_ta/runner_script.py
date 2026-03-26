import io
import tracemalloc

import python_ta


def run_runner():
    buf = io.StringIO()
    python_ta.check_all(output=buf)


tracemalloc.start()


def snapshot_runs():
    run_runner()
    s1 = tracemalloc.take_snapshot()
    run_runner()
    s2 = tracemalloc.take_snapshot()
    stats = s2.compare_to(s1, "traceback")
    for stat in stats[:10]:
        print(f"{stat.traceback.format()}")
        print(f"size_diff={stat.size_diff} | count_diff={stat.count_diff}")
    print("-" * 50)


def trace_memory_runs():
    for i in range(100):
        run_runner()
        current = tracemalloc.get_traced_memory()
        print(f" {i} | {int(current[0] / 1024 ** 2)} MB")


for i in range(5):
    snapshot_runs()
