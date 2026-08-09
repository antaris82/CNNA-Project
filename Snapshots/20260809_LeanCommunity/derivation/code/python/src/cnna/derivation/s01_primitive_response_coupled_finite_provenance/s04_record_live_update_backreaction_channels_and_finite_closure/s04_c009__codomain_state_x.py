"""Paper 1.4.4 / C009 — deterministic codomain-state assembly.

C009 is an assembly boundary, not the recurrent-closure theorem.  It consumes
one C005 state, its coherent C008 record/live channels, the C004-selected next
slot as carried by one M004 instruction, and the already-derived C016/C017
projections.  It then constructs the unique raw codomain data of that step:

* the born prefix extended by exactly the selected child;
* the immutable record channel after the instruction;
* the current live channel after the instruction.

C009 deliberately does *not* assert that this raw codomain is already another
C005 ``ResponseCapableState``.  The universal schema-closure proof belongs to
T002.  Python may realize the candidate as a C005 state as finite regression
evidence, but that executable validation is not a substitute for T002.
"""
from __future__ import annotations

from dataclasses import dataclass

from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address
from ..s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import (
    DirectedConductance,
    ResponseCapableState,
)
from ..s03_recurrent_pre_birth_measurement_and_steering.s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import (
    is_next_open_provenance_slot,
)
from ..s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import (
    DirectedRelationUpdate,
    ResponseCoupledBirthInstruction,
)
from .s01_c008__record_live_response_coupled_update import (
    RecordLiveChannels,
)
from .s02_c016__immutable_record_channel import record_channel_after_instruction
from .s03_c017__current_live_channel import live_channel_after_instruction


@dataclass(frozen=True, slots=True)
class CodomainStateData:
    """Raw deterministic output of one C009 assembly step."""

    schedule: object
    born_nonroot: tuple[Address, ...]
    record: tuple[DirectedRelationUpdate, ...]
    live: tuple[DirectedRelationUpdate, ...]


def live_channel_represents_state(
    state: ResponseCapableState,
    channels: RecordLiveChannels,
) -> bool:
    """Cross-boundary C005↔C017 coherence required at the C009 handoff.

    The current live channel must be the exact ordered representation of the
    current C005 conductance list.  This predicate first arises where C005 and
    C017 meet, so it is owned by C009 rather than retrofitted into either
    upstream node.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("C009 coherence requires a C005 ResponseCapableState")
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C009 coherence requires C008 RecordLiveChannels")
    expected = tuple(
        DirectedRelationUpdate(edge.source, edge.target, edge.value)
        for edge in state.conductances
    )
    return channels.live == expected


def assemble_codomain_state_data(
    state: ResponseCapableState,
    channels: RecordLiveChannels,
    instruction: ResponseCoupledBirthInstruction,
) -> CodomainStateData:
    """Assemble the unique raw C009 codomain data.

    No response, steering scalar, rank force, new coefficient, or iteration
    rule is introduced here.  The function rejects an incoherent C005/C017
    handoff and a non-canonical next slot, then performs only the three derived
    projections fixed by C004, C016 and C017.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("C009 requires a C005 ResponseCapableState")
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C009 requires C008 RecordLiveChannels")
    if type(instruction) is not ResponseCoupledBirthInstruction:
        raise TypeError("C009 requires an M004 ResponseCoupledBirthInstruction")
    if not live_channel_represents_state(state, channels):
        raise ValueError("C009 live channel does not represent the supplied C005 state")
    if not is_next_open_provenance_slot(state, instruction.slot):
        raise ValueError("C009 instruction does not target the canonical C004 next slot")

    return CodomainStateData(
        schedule=state.schedule,
        born_nonroot=state.born_nonroot + (instruction.slot.child,),
        record=record_channel_after_instruction(channels, instruction),
        live=live_channel_after_instruction(channels, instruction),
    )


def realize_response_capable_candidate(data: CodomainStateData) -> ResponseCapableState:
    """Finite executable realization of C009 data as a C005 state.

    Successful construction is regression evidence only.  The universal proof
    that every canonical C009 output satisfies the C005 schema is T002.
    """
    if type(data) is not CodomainStateData:
        raise TypeError("C009 realization requires CodomainStateData")
    conductances = tuple(
        DirectedConductance(update.source, update.target, update.value)
        for update in data.live
    )
    return ResponseCapableState(
        schedule=data.schedule,
        born_nonroot=data.born_nonroot,
        conductances=conductances,
    )


__all__ = [
    "CodomainStateData",
    "live_channel_represents_state",
    "assemble_codomain_state_data",
    "realize_response_capable_candidate",
]
