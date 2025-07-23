from typing import Any, Optional


class IDTracker:
    def __init__(self) -> None:
        self.id_counter: int = 0
        self.tracker: dict[int, list] = {}
        self.current_snapshot_objects: set[int] = set()

    def set_id(self, obj) -> Optional[int]:
        """Assign a unique ID to an object."""
        if self.is_tracked(id(obj)):
            return
        self.id_counter += 1
        self.tracker[id(obj)] = [self.id_counter, None]

    def get_id(self, obj) -> Optional[int]:
        """Retrieve the unique ID for an object, or none if not tracked."""
        entry = self.tracker.get(id(obj), None)
        if entry is None:
            return None
        return entry[0]

    def is_tracked(self, obj) -> bool:
        """Check if the object has already been tracked"""
        return id(obj) in self.tracker

    def set_value_entry(self, obj, value) -> None:
        """Set the value entry for an object."""
        if not self.is_tracked(obj):
            raise ValueError("Object must be tracked before setting a value entry.")
        self.tracker[id(obj)][1] = value

    def get_value_entry(self, obj) -> Optional[Any]:
        """Get the value entry for an object."""
        if not self.is_tracked(obj):
            raise ValueError("Object must be tracked before getting a value entry.")
        return self.tracker[id(obj)][1]

    def add_snapshot_object(self, obj) -> None:
        """Add an object to the current snapshot objects."""
        self.current_snapshot_objects.add(id(obj))

    def is_snapshot_object(self, obj) -> bool:
        """Check if an object is in the current snapshot objects."""
        return id(obj) in self.current_snapshot_objects

    def clear_snapshot_objects(self) -> None:
        """Clear the current snapshot objects."""
        self.current_snapshot_objects.clear()
