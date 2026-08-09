"""Paper 1.3.6 / C007 — inter-birth directed response R_n(s_{n+1}).

C007 is the first node that wires the recurrent C005 network into the exact
birth-local Schur/DtN chain.  It consumes the C004 next slot, the canonical
M001 ordered cut, M002's exact C006 domain, and C006's exact elimination.

The state-dependent operator is fixed rather than fitted.  In the M001
boundary-first/interior-second order, each directed conductance c(u,v) enters
the source/out-degree matrix

    K[u,u] += c(u,v),       K[u,v] -= c(u,v).

No symmetrization, transpose, in-degree alternative, external port, geometric
weight, numerical threshold, or steering transform is introduced.  The cut
partitions the entire already-born C005 carrier, so K is the closed current-
carrier directed Laplacian.  The unborn C004 child is absent from every matrix
coordinate.  On the exact M002 domain the response is the C006 value

    R_n(s_{n+1}) = K_BB - K_BI K_II^{-1} K_IB,

where the inverse notation denotes C006's unique exact solve, not a separate
matrix-inverse primitive.  The response is measured after birth n and before
birth n+1; C007 does not yet choose a steering functional or execute a birth.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from ..s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import Address
from ..s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import OpenBirthSlot
from .s01_c005__response_capable_state_schema_xn_n_ge_1 import ResponseCapableState
from .s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import next_open_provenance_slot
from .s03_c006__birth_local_schur_dtn_primitive import (
    InteriorNotAdmissibleError,
    OrderedSchurBlocks,
    RationalMatrix,
    schur_dtn_response,
)
from .s04_m001__canonical_birth_local_measurement_cut_cn_snplus1 import (
    BirthLocalMeasurementCut,
    canonical_birth_local_measurement_cut,
)
from .s05_m002__birth_cut_interior_domain_theorem import (
    birth_cut_interior_is_admissible,
    validate_birth_cut_block_dimensions,
)

MATRIX_CONVENTION = "source_out_degree_closed_current_carrier"


def _zero_matrix(size: int) -> list[list[Fraction]]:
    return [[Fraction(0, 1) for _ in range(size)] for _ in range(size)]


def _freeze_block(
    matrix: list[list[Fraction]],
    row_start: int,
    row_stop: int,
    col_start: int,
    col_stop: int,
) -> RationalMatrix:
    return tuple(
        tuple(matrix[i][j] for j in range(col_start, col_stop))
        for i in range(row_start, row_stop)
    )


@dataclass(frozen=True, slots=True)
class StateDirectedSchurRealization:
    """C005's exact directed matrix in the canonical M001/C006 coordinates."""

    birth_count: int
    slot: OpenBirthSlot
    cut: BirthLocalMeasurementCut
    carrier_order: tuple[Address, ...]
    full_matrix: RationalMatrix
    blocks: OrderedSchurBlocks

    def __post_init__(self) -> None:
        if type(self.birth_count) is not int or self.birth_count < 1:
            raise ValueError("C007 requires a recurrent birth count n >= 1")
        if type(self.slot) is not OpenBirthSlot:
            raise TypeError("C007 requires a C004/C018 next open slot")
        if type(self.cut) is not BirthLocalMeasurementCut:
            raise TypeError("C007 requires the canonical M001 cut")
        if self.carrier_order != self.cut.boundary + self.cut.interior:
            raise ValueError("C007 carrier order must be M001 boundary then interior")
        if self.slot.child in self.carrier_order:
            raise ValueError("C007 pre-birth matrix cannot contain the unborn child")
        size = len(self.carrier_order)
        if len(self.full_matrix) != size or any(len(row) != size for row in self.full_matrix):
            raise ValueError("C007 full matrix dimension differs from the born carrier")
        if any(sum(row, Fraction(0, 1)) != 0 for row in self.full_matrix):
            raise ValueError("C007 closed current-carrier rows must sum exactly to zero")
        validate_birth_cut_block_dimensions(self.cut, self.blocks)


@dataclass(frozen=True, slots=True)
class InterBirthDirectedResponse:
    """Exact directed response measured on X_n before the C004 child is born."""

    birth_count: int
    slot: OpenBirthSlot
    boundary: tuple[Address, ...]
    value: RationalMatrix
    realization: StateDirectedSchurRealization

    def __post_init__(self) -> None:
        if self.birth_count != self.realization.birth_count:
            raise ValueError("C007 response birth count differs from its realization")
        if self.slot != self.realization.slot:
            raise ValueError("C007 response slot differs from its realization")
        if self.boundary != self.realization.cut.boundary:
            raise ValueError("C007 response coordinates must be the M001 boundary order")
        size = len(self.boundary)
        if len(self.value) != size or any(len(row) != size for row in self.value):
            raise ValueError("C007 response dimension differs from the M001 boundary")
        if any(sum(row, Fraction(0, 1)) != 0 for row in self.value):
            raise ValueError("C007 closed directed response rows must sum exactly to zero")
        if self.slot.child in self.boundary:
            raise ValueError("C007 response boundary cannot contain the unborn child")


def state_directed_schur_realization(
    state: ResponseCapableState,
    slot: OpenBirthSlot | None = None,
) -> StateDirectedSchurRealization:
    """Assemble C005's exact source/out-degree operator in M001 block order."""
    if type(state) is not ResponseCapableState:
        raise TypeError("C007 requires a C005 ResponseCapableState")
    selected_slot = next_open_provenance_slot(state) if slot is None else slot
    cut = canonical_birth_local_measurement_cut(state, selected_slot)
    carrier_order = cut.boundary + cut.interior
    if set(carrier_order) != set(state.nodes) or len(carrier_order) != len(state.nodes):
        raise AssertionError("C007 M001 cut does not exactly cover the C005 carrier")

    position = {address: index for index, address in enumerate(carrier_order)}
    matrix = _zero_matrix(len(carrier_order))
    for edge in state.conductances:
        try:
            row = position[edge.source]
            col = position[edge.target]
        except KeyError as exc:
            raise AssertionError("C007 conductance endpoint escaped the M001 carrier") from exc
        matrix[row][row] += edge.value
        matrix[row][col] -= edge.value

    full_matrix = tuple(tuple(row) for row in matrix)
    boundary_size = len(cut.boundary)
    total_size = len(carrier_order)
    blocks = OrderedSchurBlocks(
        k_bb=_freeze_block(matrix, 0, boundary_size, 0, boundary_size),
        k_bi=_freeze_block(matrix, 0, boundary_size, boundary_size, total_size),
        k_ib=_freeze_block(matrix, boundary_size, total_size, 0, boundary_size),
        k_ii=_freeze_block(matrix, boundary_size, total_size, boundary_size, total_size),
    )
    realization = StateDirectedSchurRealization(
        birth_count=state.n,
        slot=selected_slot,
        cut=cut,
        carrier_order=carrier_order,
        full_matrix=full_matrix,
        blocks=blocks,
    )
    return realization


def inter_birth_directed_response(
    state: ResponseCapableState,
    slot: OpenBirthSlot | None = None,
) -> InterBirthDirectedResponse:
    """Compute R_n(s_{n+1}) on the exact M002/C006 partial domain."""
    realization = state_directed_schur_realization(state, slot)
    if not birth_cut_interior_is_admissible(
        state,
        realization.blocks,
        realization.slot,
    ):
        raise InteriorNotAdmissibleError(
            "C007 state-directed M001 interior is outside the exact M002 domain"
        )
    value = schur_dtn_response(realization.blocks)
    return InterBirthDirectedResponse(
        birth_count=state.n,
        slot=realization.slot,
        boundary=realization.cut.boundary,
        value=value,
        realization=realization,
    )


__all__ = [
    "MATRIX_CONVENTION",
    "StateDirectedSchurRealization",
    "InterBirthDirectedResponse",
    "state_directed_schur_realization",
    "inter_birth_directed_response",
]
