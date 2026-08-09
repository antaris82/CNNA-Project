"""Paper 1.3.5 / M002 — birth-cut interior-domain theorem.

M002 closes the domain handoff between the canonical M001 cut and the partial
C006 Schur/DtN primitive.  M001 fixes only the ordered boundary/interior carrier
partition; it does not fix numerical block entries.  Therefore universal
invertibility is not derivable from M001 alone.

The exact M002 domain is consequently the set of explicitly supplied C006
blocks whose dimensions agree with the canonical M001 cut and whose interior
system has a unique exact C006 solve.  No numerical tolerance, condition-number
threshold, regularization, or additional matrix convention is introduced.

The zero-interior case is unconditional because C006 already proves it
admissible.  For a nonempty interior, ``domain_contrast_witness`` constructs two
block assignments with the same M001 dimensions: one with identity K_II and one
with zero K_II.  The first is admissible and the second is singular.  This is an
executable obstruction to any cut-only global invertibility claim before C007
supplies the actual state-dependent matrix entries.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import OpenBirthSlot
from .s01_c005__response_capable_state_schema_xn_n_ge_1 import ResponseCapableState
from .s03_c006__birth_local_schur_dtn_primitive import (
    OrderedSchurBlocks,
    interior_is_admissible,
)
from .s04_m001__canonical_birth_local_measurement_cut_cn_snplus1 import (
    BirthLocalMeasurementCut,
    canonical_birth_local_measurement_cut,
)


def _zero_matrix(rows: int, cols: int) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(tuple(Fraction(0, 1) for _ in range(cols)) for _ in range(rows))


def _identity_matrix(size: int) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(
        tuple(Fraction(1 if i == j else 0, 1) for j in range(size))
        for i in range(size)
    )


def validate_birth_cut_block_dimensions(
    cut: BirthLocalMeasurementCut,
    blocks: OrderedSchurBlocks,
) -> None:
    """Require exact agreement between M001 coordinate counts and C006 blocks."""
    if type(cut) is not BirthLocalMeasurementCut:
        raise TypeError("M002 requires a M001 BirthLocalMeasurementCut")
    if type(blocks) is not OrderedSchurBlocks:
        raise TypeError("M002 requires C006 OrderedSchurBlocks")
    if blocks.boundary_size != len(cut.boundary):
        raise ValueError("M002 C006 boundary dimension does not match M001")
    if blocks.interior_size != len(cut.interior):
        raise ValueError("M002 C006 interior dimension does not match M001")


def birth_cut_interior_is_admissible(
    state: ResponseCapableState,
    blocks: OrderedSchurBlocks,
    slot: OpenBirthSlot | None = None,
) -> bool:
    """Exact M002 acceptance predicate on the canonical M001 cut.

    Acceptance is *exactly* C006 unique solvability after enforcing the M001
    block dimensions.  M002 adds no weaker numerical surrogate.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("M002 requires C005 ResponseCapableState")
    cut = canonical_birth_local_measurement_cut(state, slot)
    validate_birth_cut_block_dimensions(cut, blocks)
    return interior_is_admissible(blocks)


@dataclass(frozen=True, slots=True)
class DomainContrastWitness:
    """Same M001 cut dimensions with one admissible and one singular C006 input."""

    cut: BirthLocalMeasurementCut
    admissible_blocks: OrderedSchurBlocks
    inadmissible_blocks: OrderedSchurBlocks

    def __post_init__(self) -> None:
        validate_birth_cut_block_dimensions(self.cut, self.admissible_blocks)
        validate_birth_cut_block_dimensions(self.cut, self.inadmissible_blocks)
        if not interior_is_admissible(self.admissible_blocks):
            raise AssertionError("M002 admissible contrast witness is not admissible")
        if interior_is_admissible(self.inadmissible_blocks):
            raise AssertionError("M002 singular contrast witness is unexpectedly admissible")


def domain_contrast_witness(
    state: ResponseCapableState,
    slot: OpenBirthSlot | None = None,
) -> DomainContrastWitness:
    """Show that a nonempty M001 interior does not determine C006 admissibility.

    The two assignments share exactly the canonical M001 dimensions and all
    non-interior blocks are zero.  Only K_II differs: identity versus zero.
    """
    if type(state) is not ResponseCapableState:
        raise TypeError("M002 requires C005 ResponseCapableState")
    cut = canonical_birth_local_measurement_cut(state, slot)
    boundary = len(cut.boundary)
    interior = len(cut.interior)
    if interior == 0:
        raise ValueError(
            "M002 zero interior is unconditionally C006-admissible; no contrast exists"
        )

    k_bb = _zero_matrix(boundary, boundary)
    k_bi = _zero_matrix(boundary, interior)
    k_ib = _zero_matrix(interior, boundary)
    admissible = OrderedSchurBlocks(
        k_bb=k_bb,
        k_bi=k_bi,
        k_ib=k_ib,
        k_ii=_identity_matrix(interior),
    )
    inadmissible = OrderedSchurBlocks(
        k_bb=k_bb,
        k_bi=k_bi,
        k_ib=k_ib,
        k_ii=_zero_matrix(interior, interior),
    )
    return DomainContrastWitness(cut, admissible, inadmissible)


__all__ = [
    "DomainContrastWitness",
    "validate_birth_cut_block_dimensions",
    "birth_cut_interior_is_admissible",
    "domain_contrast_witness",
]
