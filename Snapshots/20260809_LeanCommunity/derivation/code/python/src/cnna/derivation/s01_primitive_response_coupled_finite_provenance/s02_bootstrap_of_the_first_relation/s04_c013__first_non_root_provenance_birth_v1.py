"""Paper 1.2.4 / C013 — first non-root provenance birth v1.

C013 is the exceptional bootstrap construction before any nontrivial network
response exists.  It consumes the structural first slot C004A, singleton seed
A001, and fixed unit normalization N001.  The seed is an explicit constructor
argument but is not retained in the generated birth state; T001 separately
proves the resulting seed-neutrality statement.

The construction is defined only when s1 lies inside the finite cutoff.  Thus
L=0 has a structural first slot but no first non-root birth.
"""
from __future__ import annotations

from dataclasses import dataclass

from .s01_c004a__first_provenance_slot_s1 import FirstProvenanceSlot
from .s02_a001__genesis_seed_star import GenesisSeed
from .s03_n001__initial_conductance_normalization_c_star_1 import InitialConductanceNormalization
from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address


@dataclass(frozen=True, slots=True)
class FirstNonRootBirth:
    """Generated C013 birth data; the bootstrap seed is deliberately absent."""

    slot: FirstProvenanceSlot
    normalization: InitialConductanceNormalization

    @property
    def root(self) -> Address:
        return self.slot.parent

    @property
    def newborn(self) -> Address:
        return self.slot.address

    @property
    def directed_relations(self) -> tuple[tuple[Address, Address], tuple[Address, Address]]:
        return ((self.root, self.newborn), (self.newborn, self.root))

    @property
    def directed_conductances(self) -> tuple[int, int]:
        return self.normalization.directed_values


def build_first_non_root_birth(
    slot: FirstProvenanceSlot,
    seed: GenesisSeed,
    normalization: InitialConductanceNormalization,
) -> FirstNonRootBirth:
    """Create v1 and the symmetric unit root-v1 relation.

    No DtN/response quantity is queried: before this relation exists there is
    no nontrivial pre-birth network response to use.
    """
    if type(slot) is not FirstProvenanceSlot:
        raise TypeError("C013 requires C004A FirstProvenanceSlot")
    if type(seed) is not GenesisSeed:
        raise TypeError("C013 requires A001 GenesisSeed")
    if type(normalization) is not InitialConductanceNormalization:
        raise TypeError("C013 requires N001 InitialConductanceNormalization")
    slot.require_admitted_address()
    return FirstNonRootBirth(slot=slot, normalization=normalization)


__all__ = ["FirstNonRootBirth", "build_first_non_root_birth"]
