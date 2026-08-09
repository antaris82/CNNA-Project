"""Paper 1.1.6 / C018 — canonical BFS/lexicographic provenance birth schedule.

Scientific contract
-------------------
C018 consumes only the already-derived finite b-ary provenance grammar C003.
It fixes a deterministic *construction convention* for open birth slots:

1. parents are visited breadth first (smaller provenance depth first);
2. parents at the same depth are visited in lexicographic address order;
3. for one parent, sibling slots are visited in increasing rank ``0,...,b-1``;
4. one slot is emitted at a time (``slot_step``).

The root already exists by C002 and is therefore not itself an open birth slot.
C018 orders possible non-root provenance births but does not assign a numerical
event index, birth time, conductance, response value, geometry, or dynamics.
The alternate ``layer_batch`` schedule remains a supplementary control and is
not implemented as an active rule here.
"""

from __future__ import annotations

from dataclasses import dataclass

from .s05_c003__finite_b_ary_provenance_grammar import (
    Address,
    FiniteBAryProvenanceGrammar,
    child_address,
)


@dataclass(frozen=True, slots=True)
class OpenBirthSlot:
    """One ordered open provenance slot: parent + local rank -> child address."""

    parent: Address
    rank: int
    child: Address


def _require_grammar(grammar: FiniteBAryProvenanceGrammar) -> FiniteBAryProvenanceGrammar:
    if type(grammar) is not FiniteBAryProvenanceGrammar:
        raise TypeError("C018 requires C003 FiniteBAryProvenanceGrammar")
    return grammar


def open_slot_key(slot: OpenBirthSlot) -> tuple[int, Address, int]:
    """Extensional BFS/lex key: parent depth, parent address, sibling rank.

    This is an ordering key only.  It is deliberately not an event index.
    """
    if type(slot) is not OpenBirthSlot:
        raise TypeError("C018 ordering requires OpenBirthSlot values")
    return (len(slot.parent), slot.parent, slot.rank)


def slot_precedes(left: OpenBirthSlot, right: OpenBirthSlot) -> bool:
    """Strict canonical slot order induced by :func:`open_slot_key`."""
    return open_slot_key(left) < open_slot_key(right)


def canonical_birth_slots(grammar: FiniteBAryProvenanceGrammar) -> tuple[OpenBirthSlot, ...]:
    """Enumerate all admissible non-root birth slots in canonical slot-step order.

    The mutable ``parent_cursor`` below is operational only: the returned tuple
    is completely determined by C003.  Children are appended to the parent
    queue exactly when their parent is processed, so queue order is breadth
    first; increasing ``grammar.slots`` gives lexicographic order within each
    layer.
    """
    grammar = _require_grammar(grammar)
    if grammar.cutoff.value == 0:
        return ()

    parents: list[Address] = [grammar.root]
    cursor = 0
    ordered: list[OpenBirthSlot] = []

    while cursor < len(parents):
        parent = parents[cursor]
        cursor += 1
        if grammar.depth(parent) >= grammar.cutoff.value:
            continue
        for rank in grammar.slots:
            child = grammar.child(parent, rank)
            ordered.append(OpenBirthSlot(parent=parent, rank=rank, child=child))
            parents.append(child)

    return tuple(ordered)


def canonical_birth_addresses(grammar: FiniteBAryProvenanceGrammar) -> tuple[Address, ...]:
    """Return the non-root child addresses in canonical birth-slot order."""
    return tuple(slot.child for slot in canonical_birth_slots(grammar))


@dataclass(frozen=True, slots=True)
class CanonicalBirthSchedule:
    """C018 rule object carrying only its C003 predecessor."""

    grammar: FiniteBAryProvenanceGrammar

    def __post_init__(self) -> None:
        _require_grammar(self.grammar)

    @property
    def slots(self) -> tuple[OpenBirthSlot, ...]:
        return canonical_birth_slots(self.grammar)

    @property
    def addresses(self) -> tuple[Address, ...]:
        return canonical_birth_addresses(self.grammar)

    def precedes(self, left: OpenBirthSlot, right: OpenBirthSlot) -> bool:
        return slot_precedes(left, right)


def build_canonical_birth_schedule(
    grammar: FiniteBAryProvenanceGrammar,
) -> CanonicalBirthSchedule:
    """Canonical constructor from the sole scientific predecessor C003."""
    return CanonicalBirthSchedule(grammar)


__all__ = [
    "CanonicalBirthSchedule",
    "OpenBirthSlot",
    "build_canonical_birth_schedule",
    "canonical_birth_addresses",
    "canonical_birth_slots",
    "open_slot_key",
    "slot_precedes",
]
