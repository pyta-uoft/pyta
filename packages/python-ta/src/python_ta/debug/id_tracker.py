from typing import Any


class IDTracker:
    """A helper class to assign and track unique integer IDs for Python objects across multiple memory model snapshots.
    Attributes:
        id_counter: Counter used to assign new unique IDs.
        tracker: Dictionary mapping object IDs to their assigned unique IDs. This allows for long-term tracking of
            objects across multiple snapshots.
        current_snapshot_objects : A set of object IDs that are currently being tracked in the current snapshot.
    """

    id_counter: int
    tracker: dict[int, int]
    current_snapshot_objects: set[int]

    def __init__(self) -> None:
        """Initialize internal counters and containers for tracking object IDs."""
        self.id_counter = 0
        self.tracker = {}
        self.current_snapshot_objects = set()

    def __getitem__(self, obj: Any) -> int:
        """Retrieve the unique ID for an object, or none if not tracked."""
        return self.tracker[id(obj)]

    def __contains__(self, obj: Any) -> bool:
        """Check if the object has already been tracked in any snapshot."""
        return id(obj) in self.tracker

    def add(self, obj: Any) -> int:
        """Assign a unique ID to an object if it is not already tracked, and add it to the current snapshot objects,
        returning the assigned ID"""
        self.current_snapshot_objects.add(id(obj))
        if obj in self:
            return self[obj]
        self.id_counter += 1
        self.tracker[id(obj)] = self.id_counter
        return self.id_counter

    def is_snapshot_object(self, obj: Any) -> bool:
        """Check if an object is in the current snapshot objects."""
        return id(obj) in self.current_snapshot_objects

    def clear_snapshot_objects(self) -> None:
        """Clear the current snapshot objects."""
        self.current_snapshot_objects.clear()
