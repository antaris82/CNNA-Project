"""Paper 1.2.3 / N001 — initial conductance normalization C★ = 1.

N001 is a fixed normalization, not a free model input.  It supplies the
unit conductance used when C013 later creates the first root–child
relation.  Directed storage starts symmetrically: both orientations carry the
same unit value.  N001 does not create endpoints, a relation, or a birth.

The exact Python integer ``1`` is only a representation of this fixed local
normalization; N001 does not choose the scalar carrier of later conductances.
The later M005 theorem owns the nontrivial claim that common positive
rescaling changes only conductance units.  This module does not pre-prove it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

C_STAR: Final[int] = 1


@dataclass(frozen=True, slots=True)
class InitialConductanceNormalization:
    """Zero-payload fixed normalization for the first directed relation."""

    @property
    def value(self) -> int:
        """Dimensionless normalization value C★."""
        return C_STAR

    @property
    def directed_values(self) -> tuple[int, int]:
        """Forward and reverse stored values before any later steering."""
        return (C_STAR, C_STAR)


INITIAL_CONDUCTANCE_NORMALIZATION: Final[InitialConductanceNormalization] = (
    InitialConductanceNormalization()
)

__all__ = [
    "C_STAR",
    "INITIAL_CONDUCTANCE_NORMALIZATION",
    "InitialConductanceNormalization",
]
