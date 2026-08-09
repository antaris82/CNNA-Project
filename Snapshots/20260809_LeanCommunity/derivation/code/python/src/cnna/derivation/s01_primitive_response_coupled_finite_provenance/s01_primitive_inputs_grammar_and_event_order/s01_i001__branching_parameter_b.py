"""Paper 1.1.1 / I001 — branching parameter ``b``.

Scientific contract
-------------------
``b`` is a free structural input satisfying exactly

    b is an integer and b >= 2.

This module deliberately provides no default value for ``b``.  Downstream
nodes must receive an explicit :class:`BranchingParameter`, so the lower-bound
condition cannot reappear as a hidden precondition in C003 or later code.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class BranchingParameter:
    """Validated carrier for the free branching input ``b``.

    Parameters
    ----------
    value:
        A built-in Python integer with ``value >= 2``.

    Notes
    -----
    ``bool`` is rejected explicitly even though Python implements ``bool`` as
    a subclass of ``int``.  This keeps the executable input domain aligned
    with the mathematical domain of natural-number branching counts.
    """

    value: int

    def __post_init__(self) -> None:
        if type(self.value) is not int:
            raise TypeError("I001 requires b to be a built-in integer")
        if self.value < 2:
            raise ValueError("I001 requires b >= 2")

    def to_int(self) -> int:
        """Return the validated branching count without an implicit coercion."""

        return self.value


__all__ = ["BranchingParameter"]
