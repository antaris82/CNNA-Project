"""Paper 1.3.1 / C005 — response-capable state schema X_n, n >= 1.

C005 is the domain schema for the recurrent growth step after the exceptional
bootstrap has ended.  A state contains a canonical C018 schedule, the non-root
addresses already born as an initial schedule prefix, and the current positive
directed conductances on the born carrier.

The schema deliberately does not compute a response, choose the next slot, or
apply a birth/update law.  Those belong to C004, M001/C006/C007 and M004/C008.
Record/live channel semantics are also downstream; C005 represents the current
response-capable network seen by the pre-birth measurement.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address
from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import CanonicalBirthSchedule
from ..s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import BootstrapState


@dataclass(frozen=True, slots=True)
class DirectedConductance:
    source: Address
    target: Address
    value: Fraction

    def __post_init__(self) -> None:
        if type(self.source) is not tuple or type(self.target) is not tuple:
            raise TypeError("C005 conductance endpoints must be provenance addresses")
        if self.source == self.target:
            raise ValueError("C005 does not store self-loop conductances")
        if type(self.value) is not Fraction:
            raise TypeError("C005 conductance values must be exact Fractions")
        if self.value <= 0:
            raise ValueError("C005 stores only positive directed conductances")


@dataclass(frozen=True, slots=True)
class ResponseCapableState:
    """Current finite weighted provenance state after n >= 1 non-root births."""

    schedule: CanonicalBirthSchedule
    born_nonroot: tuple[Address, ...]
    conductances: tuple[DirectedConductance, ...]

    def __post_init__(self) -> None:
        if type(self.schedule) is not CanonicalBirthSchedule:
            raise TypeError("C005 requires the canonical C018 schedule")
        if type(self.born_nonroot) is not tuple or not self.born_nonroot:
            raise ValueError("C005 requires at least one non-root birth (n >= 1)")
        if type(self.conductances) is not tuple:
            raise TypeError("C005 conductances must be an immutable tuple")

        expected = self.schedule.addresses[: len(self.born_nonroot)]
        if self.born_nonroot != expected:
            raise ValueError("C005 born addresses must be the initial C018 schedule prefix")
        if len(self.born_nonroot) > len(self.schedule.addresses):
            raise ValueError("C005 birth count exceeds the finite schedule")

        node_set = set(self.nodes)
        seen_pairs: set[tuple[Address, Address]] = set()
        for edge in self.conductances:
            if type(edge) is not DirectedConductance:
                raise TypeError("C005 requires DirectedConductance entries")
            if edge.source not in node_set or edge.target not in node_set:
                raise ValueError("C005 conductance endpoint is not yet born")
            pair = (edge.source, edge.target)
            if pair in seen_pairs:
                raise ValueError("C005 stores at most one conductance per ordered pair")
            seen_pairs.add(pair)

        # Every non-root node must remain connected to its provenance parent in
        # both directed orientations.  Extra positive born-born edges are allowed.
        for child in self.born_nonroot:
            parent = self.grammar.parent(child)
            if parent not in node_set:
                raise ValueError("C005 born carrier is not provenance-parent closed")
            if (parent, child) not in seen_pairs or (child, parent) not in seen_pairs:
                raise ValueError("C005 requires both directed parent-child conductances")

    @property
    def grammar(self):
        return self.schedule.grammar

    @property
    def n(self) -> int:
        """Number of non-root births already present."""
        return len(self.born_nonroot)

    @property
    def root(self) -> Address:
        return self.grammar.root

    @property
    def nodes(self) -> tuple[Address, ...]:
        return (self.root,) + self.born_nonroot

    def conductance(self, source: Address, target: Address) -> Fraction | None:
        for edge in self.conductances:
            if edge.source == source and edge.target == target:
                return edge.value
        return None


def response_capable_state_from_bootstrap(state: BootstrapState) -> ResponseCapableState:
    """Embed C014's X1 as the base case of the recurrent C005 schema."""
    if type(state) is not BootstrapState:
        raise TypeError("C005 base case requires C014 BootstrapState")
    schedule = state.birth.slot.schedule
    edges = tuple(
        DirectedConductance(source, target, Fraction(value, 1))
        for (source, target), value in zip(
            state.directed_relations,
            state.directed_conductances,
            strict=True,
        )
    )
    return ResponseCapableState(
        schedule=schedule,
        born_nonroot=(state.newborn,),
        conductances=edges,
    )


__all__ = [
    "DirectedConductance",
    "ResponseCapableState",
    "response_capable_state_from_bootstrap",
]
