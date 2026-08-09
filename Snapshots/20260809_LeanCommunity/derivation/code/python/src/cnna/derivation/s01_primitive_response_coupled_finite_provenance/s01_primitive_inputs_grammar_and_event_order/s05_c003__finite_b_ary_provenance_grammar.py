"""Paper 1.1.5 / C003 — finite b-ary provenance grammar.

Scientific contract
-------------------
Given the already-born root carrier (C002), branching input ``b >= 2``
(I001), and finite cutoff ``L >= 0`` (I002):

* the local slot alphabet is ``S_b = {0, ..., b-1}``;
* a provenance address is a finite word over ``S_b``;
* the C002 root is anchored to the empty word ``()``;
* a child in slot/rank ``r`` has address ``u + (r,)``;
* every non-root word has the unique prefix parent obtained by deleting its
  final rank, and that final rank is its sibling-rank label;
* intrinsic provenance depth is word length;
* the finite approximant admits only words of depth at most ``L``.

The local word constructor itself is independent of ``L``: terminal depth is a
finite truncation, not a change of the b-ary slot alphabet.  This module owns
no birth/event order, node id, geometry, conductance, response, or dynamics.
C018 separately owns the canonical event schedule.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from .s01_i001__branching_parameter_b import BranchingParameter
from .s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from .s04_c002__root_genesis_r import ROOT, Root, RootedCarrier

Address: TypeAlias = tuple[int, ...]


def slot_alphabet(branching: BranchingParameter) -> tuple[int, ...]:
    """Return the intrinsic local rank alphabet ``(0, ..., b-1)``."""
    if type(branching) is not BranchingParameter:
        raise TypeError("C003 requires I001 BranchingParameter")
    return tuple(range(branching.value))


def validate_unbounded_address(branching: BranchingParameter, address: Address) -> Address:
    """Validate a finite provenance word without applying the cutoff ``L``."""
    if type(branching) is not BranchingParameter:
        raise TypeError("C003 requires I001 BranchingParameter")
    if type(address) is not tuple:
        raise TypeError("C003 addresses must be built-in tuples")
    for rank in address:
        if type(rank) is not int:
            raise TypeError("C003 slot/rank labels must be built-in integers")
        if rank < 0 or rank >= branching.value:
            raise ValueError("C003 slot/rank label is outside S_b")
    return address


def root_address() -> Address:
    """Return the empty provenance word ``epsilon``."""
    return ()


def child_address(branching: BranchingParameter, parent: Address, rank: int) -> Address:
    """Append exactly one validated local slot; this operation does not inspect ``L``."""
    parent = validate_unbounded_address(branching, parent)
    if type(rank) is not int:
        raise TypeError("C003 slot/rank labels must be built-in integers")
    if rank < 0 or rank >= branching.value:
        raise ValueError("C003 slot/rank label is outside S_b")
    return parent + (rank,)


def address_parent(branching: BranchingParameter, address: Address) -> Address:
    """Return the unique prefix parent of a non-root provenance word."""
    address = validate_unbounded_address(branching, address)
    if not address:
        raise ValueError("C003 root address has no provenance parent")
    return address[:-1]


def final_slot(branching: BranchingParameter, address: Address) -> int:
    """Return the final child-slot/sibling-rank label of a non-root word."""
    address = validate_unbounded_address(branching, address)
    if not address:
        raise ValueError("C003 root address has no final slot/rank")
    return address[-1]


def address_depth(branching: BranchingParameter, address: Address) -> int:
    """Return intrinsic provenance depth, i.e. word length."""
    return len(validate_unbounded_address(branching, address))


def is_parent_of(branching: BranchingParameter, parent: Address, child: Address) -> bool:
    """Test the immediate provenance-parent relation induced by word extension."""
    parent = validate_unbounded_address(branching, parent)
    child = validate_unbounded_address(branching, child)
    return bool(child) and child[:-1] == parent


@dataclass(frozen=True, slots=True)
class FiniteBAryProvenanceGrammar:
    """C002 root anchor plus validated inputs ``b`` and ``L``.

    No fourth scientific input is introduced.  ``rooted_carrier`` is the
    already-constructed C002 predecessor, not a free parameter.
    """

    rooted_carrier: RootedCarrier
    branching: BranchingParameter
    cutoff: FiniteApproximantDepth

    def __post_init__(self) -> None:
        if type(self.rooted_carrier) is not RootedCarrier:
            raise TypeError("C003 requires the C002 RootedCarrier")
        if not self.rooted_carrier.contains_node(ROOT):
            raise ValueError("C003 requires the C002 canonical root")
        if type(self.branching) is not BranchingParameter:
            raise TypeError("C003 requires I001 BranchingParameter")
        if type(self.cutoff) is not FiniteApproximantDepth:
            raise TypeError("C003 requires I002 FiniteApproximantDepth")

    @property
    def slots(self) -> tuple[int, ...]:
        return slot_alphabet(self.branching)

    def root_address_for(self, root: Root) -> Address:
        """Anchor the unique C002 root token to the empty provenance word."""
        if type(root) is not Root or root != ROOT:
            raise TypeError("C003 root anchor requires the C002 Root token")
        return root_address()

    @property
    def root(self) -> Address:
        return self.root_address_for(ROOT)

    def validate_address(self, address: Address) -> Address:
        """Validate the b-ary word rule and the finite depth bound ``|a| <= L``."""
        address = validate_unbounded_address(self.branching, address)
        if len(address) > self.cutoff.value:
            raise ValueError("C003 address depth exceeds finite cutoff L")
        return address

    def child(self, parent: Address, rank: int) -> Address:
        """Construct an admitted finite child when successor depth is within ``L``."""
        parent = self.validate_address(parent)
        if len(parent) >= self.cutoff.value:
            raise ValueError("C003 cannot extend an admitted word beyond cutoff L")
        return self.validate_address(child_address(self.branching, parent, rank))

    def parent(self, address: Address) -> Address:
        address = self.validate_address(address)
        return address_parent(self.branching, address)

    def rank(self, address: Address) -> int:
        address = self.validate_address(address)
        return final_slot(self.branching, address)

    def depth(self, address: Address) -> int:
        address = self.validate_address(address)
        return len(address)

    def parent_relation(self, parent: Address, child: Address) -> bool:
        parent = self.validate_address(parent)
        child = self.validate_address(child)
        return is_parent_of(self.branching, parent, child)


def build_finite_b_ary_provenance_grammar(
    rooted_carrier: RootedCarrier,
    branching: BranchingParameter,
    cutoff: FiniteApproximantDepth,
) -> FiniteBAryProvenanceGrammar:
    """Canonical constructor joining the three direct predecessors of C003."""
    return FiniteBAryProvenanceGrammar(rooted_carrier, branching, cutoff)


__all__ = [
    "Address",
    "FiniteBAryProvenanceGrammar",
    "address_depth",
    "address_parent",
    "build_finite_b_ary_provenance_grammar",
    "child_address",
    "final_slot",
    "is_parent_of",
    "root_address",
    "slot_alphabet",
    "validate_unbounded_address",
]
