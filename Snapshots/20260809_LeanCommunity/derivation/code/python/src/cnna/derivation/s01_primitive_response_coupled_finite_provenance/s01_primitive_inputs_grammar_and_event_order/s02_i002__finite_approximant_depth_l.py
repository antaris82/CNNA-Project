"""Paper 1.1.2 / I002 — finite approximant depth ``L``.

Scientific contract
-------------------
``L`` is a free finite-depth input satisfying exactly

    L is a nonnegative integer.

Equivalently, ``L`` is a natural number when natural numbers include zero.
This module deliberately provides no default value and no infinity sentinel.
``L`` is a terminal provenance-depth cutoff; it is not a spatial coordinate.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class FiniteApproximantDepth:
    """Validated carrier for the free finite approximant depth ``L``.

    Parameters
    ----------
    value:
        A built-in Python integer with ``value >= 0``.

    Notes
    -----
    ``bool`` is rejected explicitly even though Python implements ``bool`` as
    a subclass of ``int``.  No float, string, ``None``, negative integer, or
    infinity-like sentinel is admitted at this scientific input boundary.
    """

    value: int

    def __post_init__(self) -> None:
        if type(self.value) is not int:
            raise TypeError("I002 requires L to be a built-in integer")
        if self.value < 0:
            raise ValueError("I002 requires L >= 0")

    def to_int(self) -> int:
        """Return the validated finite terminal depth without coercion."""

        return self.value


__all__ = ["FiniteApproximantDepth"]
