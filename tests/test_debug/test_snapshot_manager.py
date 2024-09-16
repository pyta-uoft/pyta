import os.path

from python_ta.debug import SnapshotManager

expected_result_dir = "snapshot_manager_testing_snapshots"


# TODO: tests like these can make the suite pretty slow
def test_one_line(tmp_path) -> None:
    with SnapshotManager() as manager:
        num = 123
    # TODO:  use manager to get the number of expected files
    snapshot_count = manager.get_snapshot_count()
    assert all(
        os.path.exists(f"{tmp_path.name}/snapshot-{snapshot_count}.svg")
        for i in range(snapshot_count)
    )
    for i in range(snapshot_count):
        with (
            open(f"{tmp_path.name}/snapshot-{i}.svg", mode="r", encoding="utf-8") as actual_file,
            open(
                f"snapshot_manager_testing_snapshots/one_line/snapshot-{i}.svg",
                mode="r",
                encoding="utf-8",
            ) as expected_file,
        ):
            actual_svg = actual_file.read()
            expected_svg = expected_file.read()
            assert actual_svg == expected_svg


# TODO: use temporary folder for the outputs
# def test_two_lines() -> None:
#     with SnapshotManager() as manager:
#         num = 123
#         some_string = "Hello, world"
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
#
# def test_three_lines() -> None:
#     with SnapshotManager() as manager:
#         num = 123
#         some_string = "Hello, world"
#         num2 = 321
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
# def test_for_loop() -> None:
#     with SnapshotManager():
#         nums = [1, 2, 3]
#         for num in nums:
#             a = num + 1
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
# def test_for_loop_mutation() -> None:
#     with SnapshotManager():
#         nums = [1, 2, 3]
#         for i in range(len(nums)):
#             nums[i] = nums[i] + 1
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
# def test_if_else() -> None:
#     # TODO: we are taking a snapshot even for statements, clarify if this is necessary
#     with SnapshotManager():
#         num = 10
#         if num > 5:
#             result = "greater"
#         else:
#             result = "lesser"
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
#
# def test_while_loop() -> None:
#     line_count = 2
#     with SnapshotManager():
#         num = 0
#         while num < 3:
#             num += 1
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
#
# def test_nested_loops() -> None:
#     line_count = 2
#     with SnapshotManager():
#         for i in range(3):
#             for j in range(2):
#                 result = i * j
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
#
# def test_list_comprehension() -> None:
#     line_count = 2
#     with SnapshotManager():
#         nums = [1, 2, 3, 4]
#         squares = [num * num for num in nums]
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
#
# def test_dict_comprehension() -> None:
#     line_count = 2
#     with SnapshotManager():
#         nums = [1, 2, 3, 4]
#         squares_dict = {num: num * num for num in nums}
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
#
#
# def test_try_except() -> None:
#     line_count = 2
#     with SnapshotManager():
#         try:
#             result = 10 / 0
#         except ZeroDivisionError:
#             result = "error"
#
#     assert all(os.path.exists("snapshot-1.svg") for i in range(line_count))
