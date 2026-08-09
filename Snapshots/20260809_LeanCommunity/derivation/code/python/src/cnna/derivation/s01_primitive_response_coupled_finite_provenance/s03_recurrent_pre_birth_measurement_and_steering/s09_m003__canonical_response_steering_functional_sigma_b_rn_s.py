"""Paper 1.3.9 / M003 — canonical response-steering functional.

M003 closes the scalar-extraction gap between the exact C007 inter-birth
response and the later M004 birth law.  For the C004 slot ``s=(parent, rank,
child)``, M001 places ``parent`` in the response boundary.  M003 extracts the
parent-port self-response, normalizes it by the fixed N001/M005 conductance unit
``C★ = 1``, and applies C015's fixed identity convention ``phi(x)=x``:

    Sigma_b[R_n, s] = phi(R_n[parent,parent] / C★)
                      = R_n[parent,parent].

The executable definition is written as the sum of all diagonal entries whose
boundary address equals the slot parent.  A valid C005/M001 boundary contains
that address exactly once; the aggregate form makes the Python and Lean
functional extensional without introducing a separately chosen matrix index.

No numerical sibling rank, rank bias, forward/backward bias, fitted sign,
coefficient, clipping, logarithm, saturation, birth event, conductance update,
or successor state belongs to this node.  M004 alone owns the use of the
resulting scalar in the next birth.

The functional is defined on every exact C007 response.  Positivity of its
parent-port value is a separate directed-Kron closure obligation: current
finite probes are positive, but Python evidence is not promoted to a universal
mathematical theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import (
    INITIAL_CONDUCTANCE_NORMALIZATION,
)
from ..s02_bootstrap_of_the_first_relation.s06_m005__conductance_unit_normalization_independence import (
    n001_normalized_response,
)
from .s06_c007__inter_birth_directed_response_rn_snplus1 import (
    InterBirthDirectedResponse,
)
from .s08_c015__active_linear_steering_mode_phi_x_x import (
    active_linear_steering,
)


@dataclass(frozen=True, slots=True)
class CanonicalResponseSteering:
    """Exact M003 value and its canonical C007/M001 provenance anchors."""

    birth_count: int
    slot_parent: tuple[int, ...]
    matching_boundary_indices: tuple[int, ...]
    parent_self_response: Fraction
    normalized_response: Fraction
    value: Fraction

    def __post_init__(self) -> None:
        if type(self.birth_count) is not int or self.birth_count < 1:
            raise ValueError("M003 requires a recurrent response with n >= 1")
        if len(self.matching_boundary_indices) != 1:
            raise ValueError(
                "M003 requires the slot parent exactly once in the M001 boundary"
            )
        if self.normalized_response != self.parent_self_response:
            raise ValueError("M003 C★=1 normalization must preserve the exact value")
        if self.value != self.normalized_response:
            raise ValueError("M003 C015 identity convention must preserve the exact value")

    @property
    def is_positive(self) -> bool:
        """Whether this exact representative lies in the active M004 domain."""
        return self.value > 0


def is_positive_response_steering(
    steering: CanonicalResponseSteering,
    /,
) -> bool:
    """Check the active strict-positivity handoff without claiming a theorem."""
    if type(steering) is not CanonicalResponseSteering:
        raise TypeError("M003 positivity check requires CanonicalResponseSteering")
    return steering.is_positive


def parent_port_self_response(response: InterBirthDirectedResponse, /) -> tuple[tuple[int, ...], Fraction]:
    """Return the unique parent-port diagonal aggregate from the C007 response."""
    if type(response) is not InterBirthDirectedResponse:
        raise TypeError("M003 requires a C007 InterBirthDirectedResponse")

    parent = response.slot.parent
    matching = tuple(
        index for index, address in enumerate(response.boundary) if address == parent
    )
    if len(matching) != 1:
        raise ValueError(
            "M003 requires the C004 slot parent exactly once in the M001 boundary"
        )
    value = sum((response.value[index][index] for index in matching), Fraction(0, 1))
    return matching, value


def canonical_response_steering_functional(
    response: InterBirthDirectedResponse,
    /,
) -> CanonicalResponseSteering:
    """Evaluate ``Sigma_b[R_n,s]`` on the exact C007 response domain."""
    matching, parent_response = parent_port_self_response(response)
    normalized = n001_normalized_response(
        parent_response,
        INITIAL_CONDUCTANCE_NORMALIZATION,
    )
    value = active_linear_steering(normalized)
    return CanonicalResponseSteering(
        birth_count=response.birth_count,
        slot_parent=response.slot.parent,
        matching_boundary_indices=matching,
        parent_self_response=parent_response,
        normalized_response=normalized,
        value=value,
    )


__all__ = [
    "CanonicalResponseSteering",
    "is_positive_response_steering",
    "parent_port_self_response",
    "canonical_response_steering_functional",
]
