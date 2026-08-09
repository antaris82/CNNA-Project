"""Paper 1.4.2 / C016 — immutable record channel.

C016 is a projection of the already-derived C008 update.  It does not invent a
second update law: it exposes the birth-time record and the result of applying
one C008 instruction to that record.  Exact prefix preservation is the local
immutability invariant available before the recurrent C009/P005 chain exists.
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


def immutable_record_channel(
    channels: RecordLiveChannels,
) -> tuple[DirectedRelationUpdate, ...]:
    """Return the C008 birth-time record without mutation or reconstruction."""
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C016 requires C008 RecordLiveChannels")
    return channels.record


def record_channel_after_instruction(
    channels: RecordLiveChannels,
    instruction: ResponseCoupledBirthInstruction,
) -> tuple[DirectedRelationUpdate, ...]:
    """Project the record after the unique C008 application of ``instruction``."""
    if type(channels) is not RecordLiveChannels:
        raise TypeError("C016 requires C008 RecordLiveChannels")
    if type(instruction) is not ResponseCoupledBirthInstruction:
        raise TypeError("C016 requires an M004 ResponseCoupledBirthInstruction")
    return apply_response_coupled_update(channels, instruction).record


__all__ = [
    "immutable_record_channel",
    "record_channel_after_instruction",
]
