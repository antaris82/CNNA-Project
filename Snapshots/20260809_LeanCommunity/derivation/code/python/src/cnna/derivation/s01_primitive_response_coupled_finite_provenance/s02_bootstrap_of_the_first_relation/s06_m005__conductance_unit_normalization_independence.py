"""Paper 1.2.6 / M005 — conductance-unit normalization independence.

M005 supplies the dimensionless scalar normalization needed downstream:
response and conductance unit are scaled together, so their ratio is unchanged.
The scale is a proof/comparison variable, not a CNNA model input.
"""
from __future__ import annotations

from fractions import Fraction
from typing import TypeAlias

from .s03_n001__initial_conductance_normalization_c_star_1 import (
    InitialConductanceNormalization,
)

ExactScalar: TypeAlias = int | Fraction


def normalized_response(response: ExactScalar, conductance_unit: ExactScalar) -> Fraction:
    """Return the exact dimensionless response ``response / conductance_unit``."""
    unit = Fraction(conductance_unit)
    if unit <= 0:
        raise ValueError("conductance_unit must be positive")
    return Fraction(response) / unit


def n001_normalized_response(
    response: ExactScalar,
    normalization: InitialConductanceNormalization,
) -> Fraction:
    """Normalize a response using the fixed N001 representative C★ = 1."""
    return normalized_response(response, normalization.value)


def common_positive_rescaling_preserves_normalized_response(
    response: ExactScalar,
    conductance_unit: ExactScalar,
    scale: ExactScalar,
) -> bool:
    """Check exact invariance under a common positive unit rescaling."""
    lam = Fraction(scale)
    if lam <= 0:
        raise ValueError("scale must be positive")
    r = Fraction(response)
    c = Fraction(conductance_unit)
    return normalized_response(r, c) == normalized_response(lam * r, lam * c)


__all__ = [
    "ExactScalar",
    "normalized_response",
    "n001_normalized_response",
    "common_positive_rescaling_preserves_normalized_response",
]
