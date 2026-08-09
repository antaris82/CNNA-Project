"""Paper 1.2.2 / A001 — genesis seed ★.

The seed is a technical singleton token used only by the downstream bootstrap
construction C013.  It carries no numerical, geometric, dynamical,
conductance, timing, address, or response information and is not a model input.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Final


@dataclass(frozen=True, slots=True)
class GenesisSeed:
    """Zero-payload singleton-valued bootstrap token."""


GENESIS_SEED: Final[GenesisSeed] = GenesisSeed()

__all__ = ["GENESIS_SEED", "GenesisSeed"]
