"""Paper 1.3.8 / C015 — active-path identity transform ``phi(x) = x``.

C015 fixes a convention at the active-path module boundary.  It is not a
runtime mode family, a selectable strategy, an input parameter, or an inference
from C007.  The public transform has exactly one positional argument and returns
the same object unchanged.

No coefficient, coercion, normalization, clipping, logarithm, saturation, sign
change, or hidden branch is introduced.  Null steering and logarithmic or
saturating robustness transforms belong to separate supplementary control
nodes and are not alternative branches of this module.
"""
from __future__ import annotations

from typing import TypeVar

ScalarT = TypeVar("ScalarT")


def active_linear_steering(response_scalar: ScalarT, /) -> ScalarT:
    """Apply the fixed identity convention without changing representation."""
    return response_scalar


__all__ = ["active_linear_steering"]
