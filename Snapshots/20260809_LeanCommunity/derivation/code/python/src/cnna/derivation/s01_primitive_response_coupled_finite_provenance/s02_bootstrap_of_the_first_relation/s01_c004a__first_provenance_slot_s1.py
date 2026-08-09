"""Paper 1.2.1 / C004A — first provenance slot s₁.

Scientific contract
-------------------
C004A consumes the already-derived finite b-ary provenance grammar C003 and
its canonical ordering convention C018.  The *first slot* is the first
combinatorial child position of the root.  Because C003 uses zero-based local
sibling ranks and C018 orders equal-parent slots by increasing rank, s₁ has
internal rank ``0`` and provenance address ``(0,)``.

The notation ``s₁`` is a one-based ordinal name for the first slot; it must not
be confused with the stored C003/C018 sibling-rank label, which is zero-based.

C004A is a provenance/address label, not a spatial position.  The structural
slot exists even when the finite cutoff is ``L = 0``; in that case its address
is not admitted into the finite approximant and no non-root birth occurs.  The
actual bootstrap birth is owned later by C013.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import (
    Address,
    FiniteBAryProvenanceGrammar,
    child_address,
)
from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import (
    CanonicalBirthSchedule,
    build_canonical_birth_schedule,
)


@dataclass(frozen=True, slots=True)
class FirstProvenanceSlot:
    """C004A value carrying exactly the two direct scientific predecessors.

    ``parent``, ``rank`` and ``address`` are derived properties, not additional
    constructor inputs.  In particular, there is no geometry, node id, event
    index, time, conductance or response payload here.
    """

    grammar: FiniteBAryProvenanceGrammar
    schedule: CanonicalBirthSchedule

    def __post_init__(self) -> None:
        if type(self.grammar) is not FiniteBAryProvenanceGrammar:
            raise TypeError("C004A requires C003 FiniteBAryProvenanceGrammar")
        if type(self.schedule) is not CanonicalBirthSchedule:
            raise TypeError("C004A requires C018 CanonicalBirthSchedule")
        if self.schedule.grammar != self.grammar:
            raise ValueError("C004A predecessors must refer to the same C003 grammar")

    @property
    def parent(self) -> Address:
        """The first slot belongs to the C003 root address ``()``."""
        return self.grammar.root

    @property
    def rank(self) -> int:
        """Zero-based sibling rank selected first by the C018 convention."""
        return self.grammar.slots[0]

    @property
    def address(self) -> Address:
        """Intrinsic provenance address of s₁, independent of the cutoff L."""
        return child_address(self.grammar.branching, self.parent, self.rank)

    @property
    def admitted_by_cutoff(self) -> bool:
        """Whether the structural slot address lies in the finite L-approximant."""
        return len(self.address) <= self.grammar.cutoff.value

    def require_admitted_address(self) -> Address:
        """Return s₁ as a finite admitted address, or reject the L=0 case.

        This is only an admissibility gate.  It does not perform the C013 birth.
        """
        if not self.admitted_by_cutoff:
            raise ValueError("C004A s1 is structural but not admitted when L = 0")
        return self.grammar.validate_address(self.address)


def build_first_provenance_slot(
    grammar: FiniteBAryProvenanceGrammar,
    schedule: CanonicalBirthSchedule,
) -> FirstProvenanceSlot:
    """Construct C004A from its two direct predecessors C003 and C018."""
    return FirstProvenanceSlot(grammar=grammar, schedule=schedule)


def build_canonical_first_provenance_slot(
    grammar: FiniteBAryProvenanceGrammar,
) -> FirstProvenanceSlot:
    """Convenience constructor using the unique active C018 schedule rule."""
    if type(grammar) is not FiniteBAryProvenanceGrammar:
        raise TypeError("C004A requires C003 FiniteBAryProvenanceGrammar")
    return build_first_provenance_slot(grammar, build_canonical_birth_schedule(grammar))


__all__ = [
    "FirstProvenanceSlot",
    "build_canonical_first_provenance_slot",
    "build_first_provenance_slot",
]
