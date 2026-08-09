"""Paper 1.3.4 / M001 — canonical birth-local measurement cut C_n(s_{n+1}).

M001 consumes exactly the recurrent C005 state X_n and the C004 next open
provenance slot s_{n+1}.  It selects an ordered boundary/interior partition of
the *already-born* carrier and introduces no response value, Schur operation,
unborn node, sampling cap, geometric radius, or extra model parameter.

The boundary is the restriction of C005's canonical current-carrier order to
the provenance roles determined by the next slot:

* the root-to-parent provenance chain of the slot parent, including both root
  and parent; and
* the already available earlier same-parent sibling slots, i.e. ranks strictly
  below the next slot rank.

The interior is the complementary ordered subsequence of the same current
carrier.  Thus boundary and interior together use every born node exactly once,
with order inherited from C005/C018 rather than chosen anew by M001.
"""
from __future__ import annotations

from dataclasses import dataclass

from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address
from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import OpenBirthSlot
from .s01_c005__response_capable_state_schema_xn_n_ge_1 import ResponseCapableState
from .s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import (
    is_next_open_provenance_slot,
    next_open_provenance_slot,
)


@dataclass(frozen=True, slots=True)
class BirthLocalMeasurementCut:
    """Ordered M001 boundary/interior blocks on the already-born carrier."""

    boundary: tuple[Address, ...]
    interior: tuple[Address, ...]

    def __post_init__(self) -> None:
        if type(self.boundary) is not tuple or type(self.interior) is not tuple:
            raise TypeError("M001 boundary and interior must be immutable tuples")
        if not self.boundary:
            raise ValueError("M001 birth-local boundary cannot be empty")
        for address in self.boundary + self.interior:
            if type(address) is not tuple:
                raise TypeError("M001 cut entries must be provenance addresses")
        if len(set(self.boundary)) != len(self.boundary):
            raise ValueError("M001 boundary contains duplicate addresses")
        if len(set(self.interior)) != len(self.interior):
            raise ValueError("M001 interior contains duplicate addresses")
        if set(self.boundary) & set(self.interior):
            raise ValueError("M001 boundary and interior must be disjoint")


def causal_predecessor_ports(slot: OpenBirthSlot) -> tuple[Address, ...]:
    """Return root-to-parent prefixes fixed by the slot's provenance address."""
    if type(slot) is not OpenBirthSlot:
        raise TypeError("M001 requires a C018 OpenBirthSlot")
    parent = slot.parent
    return tuple(parent[:depth] for depth in range(len(parent) + 1))


def older_sibling_ports(slot: OpenBirthSlot) -> tuple[Address, ...]:
    """Return same-parent child addresses with C018 ranks strictly below slot.rank."""
    if type(slot) is not OpenBirthSlot:
        raise TypeError("M001 requires a C018 OpenBirthSlot")
    return tuple(slot.parent + (rank,) for rank in range(slot.rank))


def is_birth_local_port(slot: OpenBirthSlot, address: Address) -> bool:
    """Provenance-only boundary predicate used by both constructor and audit."""
    if type(address) is not tuple:
        raise TypeError("M001 boundary predicate expects a provenance address")
    return address in causal_predecessor_ports(slot) or address in older_sibling_ports(slot)


def is_canonical_birth_local_measurement_cut(
    state: ResponseCapableState,
    slot: OpenBirthSlot,
    cut: BirthLocalMeasurementCut,
) -> bool:
    """Extensional M001 predicate independent of any Schur/DtN calculation."""
    if type(state) is not ResponseCapableState:
        raise TypeError("M001 requires C005 ResponseCapableState")
    if type(slot) is not OpenBirthSlot:
        raise TypeError("M001 requires a C018 OpenBirthSlot")
    if type(cut) is not BirthLocalMeasurementCut:
        raise TypeError("M001 candidate must be BirthLocalMeasurementCut")
    if not is_next_open_provenance_slot(state, slot):
        return False

    expected_boundary = tuple(node for node in state.nodes if is_birth_local_port(slot, node))
    expected_interior = tuple(node for node in state.nodes if not is_birth_local_port(slot, node))
    return cut.boundary == expected_boundary and cut.interior == expected_interior


def canonical_birth_local_measurement_cut(
    state: ResponseCapableState,
    slot: OpenBirthSlot | None = None,
) -> BirthLocalMeasurementCut:
    """Construct the unique M001 cut for the C004 successor of X_n.

    If ``slot`` is omitted, C004 is invoked to obtain the unique successor.  If
    it is supplied, it must itself satisfy the C004 least-open predicate; M001
    never accepts a later open slot or an unborn address as an alternate cut
    selector.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("M001 requires C005 ResponseCapableState")
    if slot is None:
        slot = next_open_provenance_slot(state)
    elif type(slot) is not OpenBirthSlot:
        raise TypeError("M001 requires a C018 OpenBirthSlot")
    elif not is_next_open_provenance_slot(state, slot):
        raise ValueError("M001 supplied slot is not the C004 next open provenance slot")

    causal = causal_predecessor_ports(slot)
    siblings = older_sibling_ports(slot)
    born = set(state.nodes)

    # These are C004/C005 consequences.  Keep them executable so a future
    # upstream semantic drift fails at the handoff rather than inside C006.
    missing_causal = tuple(a for a in causal if a not in born)
    missing_siblings = tuple(a for a in siblings if a not in born)
    if missing_causal:
        raise AssertionError("M001 C004/C005 handoff lost a causal predecessor")
    if missing_siblings:
        raise AssertionError("M001 C004/C005 handoff lost an earlier sibling")
    if slot.child in born:
        raise AssertionError("M001 pre-birth cut must not contain the unborn C004 child")

    boundary = tuple(node for node in state.nodes if is_birth_local_port(slot, node))
    interior = tuple(node for node in state.nodes if not is_birth_local_port(slot, node))
    cut = BirthLocalMeasurementCut(boundary=boundary, interior=interior)

    if state.root not in cut.boundary:
        raise AssertionError("M001 canonical boundary must retain the provenance root")
    if slot.parent not in cut.boundary:
        raise AssertionError("M001 canonical boundary must retain the C004 parent")
    if slot.child in cut.boundary or slot.child in cut.interior:
        raise AssertionError("M001 cut contains the unborn C004 child")
    if set(cut.boundary) | set(cut.interior) != born:
        raise AssertionError("M001 cut does not partition the C005 born carrier")
    if not is_canonical_birth_local_measurement_cut(state, slot, cut):
        raise AssertionError("M001 constructor failed its extensional semantic predicate")
    return cut


__all__ = [
    "BirthLocalMeasurementCut",
    "causal_predecessor_ports",
    "older_sibling_ports",
    "is_birth_local_port",
    "is_canonical_birth_local_measurement_cut",
    "canonical_birth_local_measurement_cut",
]
