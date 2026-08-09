"""Paper 1.3.10 / M004 — response-coupled birth law ``B_b``.

M004 is the deterministic bridge from the actual C005/C004/C007/M003 pre-birth
objects to one immutable response-derived birth instruction. O001 has already
removed every independent rank, forward, and backward bias channel. Provenance
fixes only the support of the instruction:

* the direct parent/newborn relation in both orientations;
* a live newborn-to-strict-ancestor backreaction;
* live relations in both orientations with already-born earlier siblings; and
* the response-derived birth lapse.

The direct parameter-free lift is an algebraic zero-inclusive map: it transports
the same exact value ``sigma = Sigma_b[R_n,s]`` to every listed channel for
``sigma >= 0``.  Its zero boundary annihilates all response-derived relation
values and the lapse.  The active recurrent birth law is stricter: because C005
stores only positive directed conductances, it admits only ``sigma > 0``.  A proof
that every reachable C007/M003 response satisfies this strict inequality is a
separate directed-Kron positivity closure obligation; it is not manufactured by
M004.
No sibling rank, rank distance, depth attenuation, mode, fitted sign, baseline,
normalization, clipping, node ``g`` load, or free coefficient changes the value.

M004 does not mutate the state, advance a stored birth counter, or create a
separate newborn scalar. C008 alone owns application to record/live state; C011
owns later lapse semantics.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address
from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import OpenBirthSlot
from .s01_c005__response_capable_state_schema_xn_n_ge_1 import ResponseCapableState
from .s04_m001__canonical_birth_local_measurement_cut_cn_snplus1 import (
    causal_predecessor_ports,
    older_sibling_ports,
)
from .s06_c007__inter_birth_directed_response_rn_snplus1 import (
    InterBirthDirectedResponse,
    inter_birth_directed_response,
)
from .s07_o001__ist_response_independent_directed_bias_obstruction import (
    AdmittedGrowthLawInputs,
    CandidateGrowthLawInputs,
    NO_INDEPENDENT_DIRECTED_BIAS,
    admit_growth_law_inputs,
)
from .s09_m003__canonical_response_steering_functional_sigma_b_rn_s import (
    CanonicalResponseSteering,
    canonical_response_steering_functional,
    is_positive_response_steering,
)


class BirthLawDomainError(ValueError):
    """Raised when supplied objects are not one canonical active positive M004 input."""


@dataclass(frozen=True, slots=True)
class DirectedRelationUpdate:
    """One exact directed relation instruction; C008 later applies it."""

    source: Address
    target: Address
    value: Fraction

    def __post_init__(self) -> None:
        if type(self.source) is not tuple or type(self.target) is not tuple:
            raise TypeError("M004 relation endpoints must be provenance addresses")
        if self.source == self.target:
            raise ValueError("M004 does not emit self-loop relation updates")
        if type(self.value) is not Fraction:
            raise TypeError("M004 relation values must be exact Fractions")
        if self.value < 0:
            raise ValueError("M004 direct-lift relation values must be nonnegative")


@dataclass(frozen=True, slots=True)
class ResponseCoupledBirthInstruction:
    """Complete immutable M004 channel assignment before the C008 update."""

    slot: OpenBirthSlot
    steering_value: Fraction
    parent_child_birth_updates: tuple[DirectedRelationUpdate, ...]
    ancestor_backreaction_updates: tuple[DirectedRelationUpdate, ...]
    sibling_backreaction_updates: tuple[DirectedRelationUpdate, ...]
    birth_lapse: Fraction

    def __post_init__(self) -> None:
        if type(self.slot) is not OpenBirthSlot:
            raise TypeError("M004 requires the canonical C004/C018 slot")
        if type(self.steering_value) is not Fraction:
            raise TypeError("M004 requires an exact M003 steering Fraction")
        if self.steering_value < 0:
            raise ValueError("M004 requires a nonnegative M003 steering value")
        if type(self.birth_lapse) is not Fraction:
            raise TypeError("M004 birth lapse must be an exact Fraction")
        if self.birth_lapse != self.steering_value:
            raise ValueError("M004 birth lapse must equal the unmodified M003 value")

        expected_parent_child = (
            DirectedRelationUpdate(self.slot.parent, self.slot.child, self.steering_value),
            DirectedRelationUpdate(self.slot.child, self.slot.parent, self.steering_value),
        )
        if self.parent_child_birth_updates != expected_parent_child:
            raise ValueError("M004 parent-child support/value drift")

        strict_ancestors = causal_predecessor_ports(self.slot)[:-1]
        expected_ancestors = tuple(
            DirectedRelationUpdate(self.slot.child, ancestor, self.steering_value)
            for ancestor in strict_ancestors
        )
        if self.ancestor_backreaction_updates != expected_ancestors:
            raise ValueError("M004 ancestor backreaction support/value drift")

        expected_siblings = tuple(
            update
            for sibling in older_sibling_ports(self.slot)
            for update in (
                DirectedRelationUpdate(sibling, self.slot.child, self.steering_value),
                DirectedRelationUpdate(self.slot.child, sibling, self.steering_value),
            )
        )
        if self.sibling_backreaction_updates != expected_siblings:
            raise ValueError("M004 sibling backreaction support/value drift")

    @property
    def all_relation_updates(self) -> tuple[DirectedRelationUpdate, ...]:
        """All relation channels; the lapse remains a separate scalar channel."""
        return (
            self.parent_child_birth_updates
            + self.ancestor_backreaction_updates
            + self.sibling_backreaction_updates
        )


def direct_response_lift(
    slot: OpenBirthSlot,
    steering_value: Fraction,
    /,
) -> ResponseCoupledBirthInstruction:
    """Evaluate the pure structured lift ``B_b(sigma)`` on one provenance slot.

    This is the exact zero-inclusive channel map. The canonical C005/C007/M003
    dependency validation is performed separately by
    :func:`canonical_bias_free_birth_law_inputs`.
    """
    if type(slot) is not OpenBirthSlot:
        raise TypeError("M004 direct lift requires one canonical OpenBirthSlot")
    if type(steering_value) is not Fraction:
        raise TypeError("M004 direct lift requires an exact Fraction")
    if steering_value < 0:
        raise BirthLawDomainError("M004 exact domain requires Sigma_b >= 0")

    parent_child = (
        DirectedRelationUpdate(slot.parent, slot.child, steering_value),
        DirectedRelationUpdate(slot.child, slot.parent, steering_value),
    )
    ancestors = tuple(
        DirectedRelationUpdate(slot.child, ancestor, steering_value)
        for ancestor in causal_predecessor_ports(slot)[:-1]
    )
    siblings = tuple(
        update
        for sibling in older_sibling_ports(slot)
        for update in (
            DirectedRelationUpdate(sibling, slot.child, steering_value),
            DirectedRelationUpdate(slot.child, sibling, steering_value),
        )
    )
    return ResponseCoupledBirthInstruction(
        slot=slot,
        steering_value=steering_value,
        parent_child_birth_updates=parent_child,
        ancestor_backreaction_updates=ancestors,
        sibling_backreaction_updates=siblings,
        birth_lapse=steering_value,
    )


def canonical_bias_free_birth_law_inputs(
    state: ResponseCapableState,
    response: InterBirthDirectedResponse,
    steering: CanonicalResponseSteering,
    /,
) -> AdmittedGrowthLawInputs[
    ResponseCapableState,
    OpenBirthSlot,
    InterBirthDirectedResponse,
    CanonicalResponseSteering,
]:
    """Validate and admit exactly the C005/C004/C007/M003 input tuple."""
    if type(state) is not ResponseCapableState:
        raise TypeError("M004 requires a C005 ResponseCapableState")
    if type(response) is not InterBirthDirectedResponse:
        raise TypeError("M004 requires a C007 InterBirthDirectedResponse")
    if type(steering) is not CanonicalResponseSteering:
        raise TypeError("M004 requires a M003 CanonicalResponseSteering")

    canonical_response = inter_birth_directed_response(state)
    if response != canonical_response:
        raise BirthLawDomainError("M004 response is not the canonical C007 response of X_n")
    canonical_steering = canonical_response_steering_functional(response)
    if steering != canonical_steering:
        raise BirthLawDomainError("M004 steering is not Sigma_b of the supplied response")
    if not is_positive_response_steering(steering):
        raise BirthLawDomainError(
            "M004 active birth domain requires Sigma_b > 0; "
            "the zero lift is algebraic boundary data only"
        )

    candidate = CandidateGrowthLawInputs(
        state=state,
        slot=response.slot,
        response=response,
        steering=steering,
        independent_bias=NO_INDEPENDENT_DIRECTED_BIAS,
    )
    return admit_growth_law_inputs(candidate)


def response_coupled_birth_law(
    inputs: AdmittedGrowthLawInputs[
        ResponseCapableState,
        OpenBirthSlot,
        InterBirthDirectedResponse,
        CanonicalResponseSteering,
    ],
    /,
) -> ResponseCoupledBirthInstruction:
    """Validate the canonical tuple and apply the pure direct response lift."""
    if type(inputs) is not AdmittedGrowthLawInputs:
        raise TypeError("M004 requires O001-admitted growth-law inputs")
    canonical = canonical_bias_free_birth_law_inputs(
        inputs.state,
        inputs.response,
        inputs.steering,
    )
    if inputs != canonical or inputs.slot != inputs.response.slot:
        raise BirthLawDomainError("M004 admitted input tuple is not canonical")
    return direct_response_lift(inputs.slot, inputs.steering.value)


__all__ = [
    "BirthLawDomainError",
    "DirectedRelationUpdate",
    "ResponseCoupledBirthInstruction",
    "direct_response_lift",
    "canonical_bias_free_birth_law_inputs",
    "response_coupled_birth_law",
]
