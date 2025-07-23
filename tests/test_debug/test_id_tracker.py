import pytest

from python_ta.debug.id_tracker import IDTracker


def test_setitem_and_getitem() -> None:
    """Test assigning an ID and retrieving it using __getitem__."""
    tracker = IDTracker()
    obj = object()
    tracker.add(obj)
    assert tracker[obj] == 1


def test_setitem_incremental_ids() -> None:
    """Test that IDs are assigned incrementally."""
    tracker = IDTracker()
    obj1 = object()
    obj2 = object()
    tracker.add(obj1)
    tracker.add(obj2)
    assert tracker[obj1] == 1
    assert tracker[obj2] == 2


def test_getitem_keyerror() -> None:
    """Test that __getitem__ raises KeyError for untracked objects."""
    tracker = IDTracker()
    obj = object()
    with pytest.raises(KeyError):
        tracker[obj]


def test_contains() -> None:
    """Test the __contains__ method to check if an object is tracked."""
    tracker = IDTracker()
    obj = object()
    assert obj not in tracker
    tracker.add(obj)
    assert obj in tracker


def test_is_snapshot_object() -> None:
    """Test whether set_id correctly marks the object as part of the snapshot."""
    tracker = IDTracker()
    obj = object()
    assert not tracker.is_snapshot_object(obj)
    tracker.add(obj)
    assert tracker.is_snapshot_object(obj)


def test_clear_snapshot_objects() -> None:
    """Test that clear_snapshot_objects removes all snapshot markings."""
    tracker = IDTracker()
    obj = object()
    tracker.add(obj)
    tracker.clear_snapshot_objects()
    assert not tracker.is_snapshot_object(obj)
