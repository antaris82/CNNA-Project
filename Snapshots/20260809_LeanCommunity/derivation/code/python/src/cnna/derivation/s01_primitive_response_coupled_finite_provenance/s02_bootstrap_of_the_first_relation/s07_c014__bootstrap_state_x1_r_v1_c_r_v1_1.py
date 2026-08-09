"""Paper 1.2.7 / C014 — bootstrap state X₁.

C014 packages the already-derived exceptional first birth as the first
response-capable weighted provenance state.  The state contains exactly the
root, first newborn, both directed orientations of their relation, and the
N001 unit conductances inherited from C013.

Seed-neutrality and conductance-unit independence are certificates supplied by
T001 and M005 respectively; they are not additional runtime payload fields.
No response value is evaluated here.  "Response-capable" means that the first
nontrivial weighted relation now exists, so later response constructions have
something nontrivial to act on.
"""
from __future__ import annotations

from dataclasses import dataclass

from .s04_c013__first_non_root_provenance_birth_v1 import FirstNonRootBirth
from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address


@dataclass(frozen=True, slots=True)
class BootstrapState:
    """First weighted provenance state X₁; no seed or unit-choice variable is stored."""

    birth: FirstNonRootBirth

    def __post_init__(self) -> None:
        if type(self.birth) is not FirstNonRootBirth:
            raise TypeError("C014 requires C013 FirstNonRootBirth")

    @property
    def root(self) -> Address:
        return self.birth.root

    @property
    def newborn(self) -> Address:
        return self.birth.newborn

    @property
    def directed_relations(self) -> tuple[tuple[Address, Address], tuple[Address, Address]]:
        return self.birth.directed_relations

    @property
    def directed_conductances(self) -> tuple[int, int]:
        return self.birth.directed_conductances


def build_bootstrap_state(birth: FirstNonRootBirth) -> BootstrapState:
    """Package the completed C013 bootstrap birth as X₁."""
    return BootstrapState(birth=birth)


__all__ = ["BootstrapState", "build_bootstrap_state"]
