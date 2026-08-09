"""Paper 1.4.5 / T002 — recurrent state closure theorem.

T002 closes one canonical response-coupled recurrent step.  It consumes a C005
state together with the derived C008 record/live channels that represent its
current conductances, computes the already-defined C007/M003/M004 instruction,
uses C009 for raw codomain assembly, and realizes that codomain back into the
same C005 schema.  The updated channels are returned with the successor so the
next recurrent step has the required C009 coherence handoff.

Python is executable regression evidence.  The universal closure theorem is
owned by the Lean T002 proof and its origin-local supporting lemmas.
"""
from __future__ import annotations

from dataclasses import dataclass

from ..s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import (
    ResponseCapableState,
)
from ..s03_recurrent_pre_birth_measurement_and_steering.s06_c007__inter_birth_directed_response_rn_snplus1 import (
    inter_birth_directed_response,
)
from ..s03_recurrent_pre_birth_measurement_and_steering.s09_m003__canonical_response_steering_functional_sigma_b_rn_s import (
    canonical_response_steering_functional,
)
from ..s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import (
    canonical_bias_free_birth_law_inputs,
    response_coupled_birth_law,
)
from .s01_c008__record_live_response_coupled_update import (
    RecordLiveChannels,
    apply_response_coupled_update,
)
from .s04_c009__codomain_state_x import (
    CodomainStateData,
    assemble_codomain_state_data,
    live_channel_represents_state,
    realize_response_capable_candidate,
)


@dataclass(frozen=True, slots=True)
class RecurrentStepClosure:
    """One closed T002 handoff, including the data needed for the next step."""

    predecessor: ResponseCapableState
    raw_codomain: CodomainStateData
    successor: ResponseCapableState
    channels: RecordLiveChannels

    def __post_init__(self) -> None:
        if self.successor.n != self.predecessor.n + 1:
            raise ValueError("T002 successor must add exactly one non-root birth")
        if not live_channel_represents_state(self.successor, self.channels):
            raise ValueError("T002 successor live channel must represent successor conductances")


def recurrent_state_successor(
    state: ResponseCapableState,
    channels: RecordLiveChannels,
    /,
) -> RecurrentStepClosure:
    """Evaluate one canonical C007→M003→M004→C009 step and re-enter C005."""
    if type(state) is not ResponseCapableState:
        raise TypeError("T002 requires a C005 ResponseCapableState")
    if type(channels) is not RecordLiveChannels:
        raise TypeError("T002 requires C008 RecordLiveChannels")
    if not live_channel_represents_state(state, channels):
        raise ValueError("T002 pre-step live channel does not represent X_n")

    response = inter_birth_directed_response(state)
    steering = canonical_response_steering_functional(response)
    admitted = canonical_bias_free_birth_law_inputs(state, response, steering)
    instruction = response_coupled_birth_law(admitted)

    raw = assemble_codomain_state_data(state, channels, instruction)
    successor = realize_response_capable_candidate(raw)
    next_channels = apply_response_coupled_update(channels, instruction)

    if next_channels.record != raw.record or next_channels.live != raw.live:
        raise AssertionError("T002 C008/C009 channel assembly drift")
    if not live_channel_represents_state(successor, next_channels):
        raise AssertionError("T002 post-step C005/C017 coherence failed")

    return RecurrentStepClosure(state, raw, successor, next_channels)


__all__ = ["RecurrentStepClosure", "recurrent_state_successor"]
