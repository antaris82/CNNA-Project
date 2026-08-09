"""Paper 1.4.1 / C008 — record/live response-coupled update.

C008 consumes the immutable M004 birth instruction and applies only its derived
channel support.  The historical ``record`` channel receives the two relations
created at the birth cut.  The current ``live`` channel receives those same
birth relations plus M004's strict-ancestor and earlier-sibling backreaction.

The old channel lists are preserved as prefixes.  C008 introduces no rank,
depth, mode, attenuation, fitted coefficient, node load, or independent scalar.
It also does not construct the next C005 response-capable state; that finite
closure belongs downstream to C009/T002.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import BootstrapState
from ..s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import (
    DirectedConductance,
    response_capable_state_from_bootstrap,
)
from ..s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import (
    DirectedRelationUpdate,
    ResponseCoupledBirthInstruction,
)


@dataclass(frozen=True, slots=True)
class RecordLiveChannels:
    """Immutable historical/current relation channels at one growth stage."""

    record: tuple[DirectedRelationUpdate, ...]
    live: tuple[DirectedRelationUpdate, ...]

    def __post_init__(self) -> None:
        if type(self.record) is not tuple or type(self.live) is not tuple:
            raise TypeError("C008 record/live channels must be immutable tuples")
        if not all(type(update) is DirectedRelationUpdate for update in self.record):
            raise TypeError("C008 record entries must be M004 DirectedRelationUpdate values")
        if not all(type(update) is DirectedRelationUpdate for update in self.live):
            raise TypeError("C008 live entries must be M004 DirectedRelationUpdate values")


def _conductance_as_exact_update(edge: DirectedConductance) -> DirectedRelationUpdate:
    """Exact C005 -> C008 representation map for the exceptional X1 bootstrap."""
    if type(edge) is not DirectedConductance:
        raise TypeError("C008 bootstrap conversion requires a C005 DirectedConductance")
    return DirectedRelationUpdate(edge.source, edge.target, Fraction(edge.value))


def bootstrap_record_live_channels(state: BootstrapState) -> RecordLiveChannels:
    """Derive the initial record/live pair from the actual C014/C005 X1 state.

    This is deliberately bootstrap-specific.  A generic snapshot of a later
    live C005 state would erase the historical distinction that C008 exists to
    preserve.
    """
    if type(state) is not BootstrapState:
        raise TypeError("C008 bootstrap initialization requires C014 BootstrapState")
    x1 = response_capable_state_from_bootstrap(state)
    initial = tuple(_conductance_as_exact_update(edge) for edge in x1.conductances)
    return RecordLiveChannels(record=initial, live=initial)


def record_instruction_updates(
    instruction: ResponseCoupledBirthInstruction,
) -> tuple[DirectedRelationUpdate, ...]:
    """The immutable birth-history delta: direct parent/newborn relations only."""
    if type(instruction) is not ResponseCoupledBirthInstruction:
        raise TypeError("C008 requires an M004 ResponseCoupledBirthInstruction")
    return instruction.parent_child_birth_updates


def live_instruction_updates(
    instruction: ResponseCoupledBirthInstruction,
) -> tuple[DirectedRelationUpdate, ...]:
    """The current-network delta fixed completely by M004 support."""
    if type(instruction) is not ResponseCoupledBirthInstruction:
        raise TypeError("C008 requires an M004 ResponseCoupledBirthInstruction")
    return (
        instruction.parent_child_birth_updates
        + instruction.ancestor_backreaction_updates
        + instruction.sibling_backreaction_updates
    )


def apply_response_coupled_update(
    channels: RecordLiveChannels,
    instruction: ResponseCoupledBirthInstruction,
) -> RecordLiveChannels:
    """Append the M004-derived deltas without rewriting prior history."""
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C008 update requires RecordLiveChannels")
    if type(instruction) is not ResponseCoupledBirthInstruction:
        raise TypeError("C008 update requires an M004 ResponseCoupledBirthInstruction")
    return RecordLiveChannels(
        record=channels.record + record_instruction_updates(instruction),
        live=channels.live + live_instruction_updates(instruction),
    )


__all__ = [
    "RecordLiveChannels",
    "bootstrap_record_live_channels",
    "record_instruction_updates",
    "live_instruction_updates",
    "apply_response_coupled_update",
]
