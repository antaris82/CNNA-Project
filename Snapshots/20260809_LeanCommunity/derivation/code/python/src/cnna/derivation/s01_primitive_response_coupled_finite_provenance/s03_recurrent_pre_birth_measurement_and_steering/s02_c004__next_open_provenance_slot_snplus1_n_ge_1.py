"""Paper 1.3.2 / C004 — next open provenance slot s_{n+1}, n >= 1.

C004 consumes exactly the recurrent C005 state X_n and its already-derived
C018 canonical schedule.  Python realizes the unique mathematical object
computationally: because C005 enforces that the born non-root addresses are
exactly the first ``n`` C018 addresses, the next open slot is the zero-based
schedule entry ``schedule.slots[n]``.

The returned object is the existing C018 ``OpenBirthSlot``.  C004 adds no new
slot type, geometry, event index, time, response quantity, conductance, or
birth/update rule.  Saturation of the finite approximant is represented by
absence of a next slot, never by a sentinel slot.
"""
from __future__ import annotations

from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import (
    OpenBirthSlot,
)
from .s01_c005__response_capable_state_schema_xn_n_ge_1 import (
    ResponseCapableState,
)


def is_next_open_provenance_slot(
    state: ResponseCapableState,
    slot: OpenBirthSlot,
) -> bool:
    """Extensional C004 predicate shared with the Lean characterization.

    A candidate is the C004 slot iff it is an admissible C018 slot whose child
    is not yet born and no still-open C018 slot precedes it.  This predicate is
    deliberately independent of positional indexing and is therefore the
    cross-language semantic lock for the indexed Python implementation.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("C004 requires C005 ResponseCapableState")
    if type(slot) is not OpenBirthSlot:
        raise TypeError("C004 candidate must be a C018 OpenBirthSlot")

    schedule_slots = state.schedule.slots
    if slot not in schedule_slots:
        return False

    born = set(state.born_nonroot)
    if slot.child in born:
        return False

    for other in schedule_slots:
        if other.child not in born and state.schedule.precedes(other, slot):
            return False
    return True


def next_open_provenance_slot(state: ResponseCapableState) -> OpenBirthSlot:
    """Return the unique next C018 slot after the C005 prefix X_n.

    With ``n = len(state.born_nonroot)``, C005 supplies
    ``state.born_nonroot == state.schedule.addresses[:n]``.  Hence the next
    open slot, when it exists, is exactly ``state.schedule.slots[n]``.

    Raises
    ------
    LookupError
        If all finite C018 slots are already born.  No out-of-cutoff or
        sentinel provenance slot is synthesized.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("C004 requires C005 ResponseCapableState")

    slots = state.schedule.slots
    n = state.n
    if n >= len(slots):
        raise LookupError("C004 finite provenance schedule is saturated")

    # C005 already enforces this equality.  Keep the explicit boundary check
    # here because it is the exact semantic handoff C005 -> C004.
    expected_prefix = tuple(slot.child for slot in slots[:n])
    if state.born_nonroot != expected_prefix:
        raise AssertionError("C004 received a state that violates the C005 C018-prefix lock")

    candidate = slots[n]

    # These checks are mathematical invariants, not an alternate selection law.
    if candidate.child in state.born_nonroot:
        raise AssertionError("C004 indexed candidate is not open")
    if candidate.parent not in state.nodes:
        raise AssertionError("C004 indexed candidate has an unborn provenance parent")
    if not is_next_open_provenance_slot(state, candidate):
        raise AssertionError("C004 indexed candidate failed the extensional least-open predicate")

    return candidate


__all__ = [
    "is_next_open_provenance_slot",
    "next_open_provenance_slot",
]
