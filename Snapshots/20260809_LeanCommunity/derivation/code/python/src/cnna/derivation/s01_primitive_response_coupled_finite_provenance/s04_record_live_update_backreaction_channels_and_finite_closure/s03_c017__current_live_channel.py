"""Paper 1.4.3 / C017 — current live relation channel.

C017 projects C008's current live relation history.  It is not yet a Schur/DtN
response and not the later live-minus-record backreaction observable C024.
"""
from __future__ import annotations

from ..s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import (
    DirectedRelationUpdate,
    ResponseCoupledBirthInstruction,
)
from .s01_c008__record_live_response_coupled_update import (
    RecordLiveChannels,
    apply_response_coupled_update,
)


def current_live_channel(
    channels: RecordLiveChannels,
) -> tuple[DirectedRelationUpdate, ...]:
    """Return the current C008 live relation channel."""
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C017 requires C008 RecordLiveChannels")
    return channels.live


def live_channel_after_instruction(
    channels: RecordLiveChannels,
    instruction: ResponseCoupledBirthInstruction,
) -> tuple[DirectedRelationUpdate, ...]:
    """Project the live channel after the unique C008 application of ``instruction``."""
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C017 requires C008 RecordLiveChannels")
    if type(instruction) is not ResponseCoupledBirthInstruction:
        raise TypeError("C017 requires an M004 ResponseCoupledBirthInstruction")
    return apply_response_coupled_update(channels, instruction).live


__all__ = [
    "current_live_channel",
    "live_channel_after_instruction",
]
