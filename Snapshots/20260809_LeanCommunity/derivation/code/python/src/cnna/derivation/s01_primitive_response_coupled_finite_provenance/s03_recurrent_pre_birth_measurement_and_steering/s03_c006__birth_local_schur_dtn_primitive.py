"""Paper 1.3.3 / C006 — birth-local Schur/DtN primitive.

C006 owns only the exact algebraic elimination primitive on an explicitly
supplied ordered block matrix.  It does not choose a cut, construct a network
matrix from C005 conductances, assert that a particular M001 interior is
admissible, or define the inter-birth response R_n.  Those handoffs belong to
M001/M002/C007.

The common Python/Lean object is a rational block matrix

    K = [[K_BB, K_BI],
         [K_IB, K_II]]

with boundary coordinates first and interior coordinates second.  On the exact
partial domain where K_II X = K_IB has a unique solution X, the Schur/DtN
response is

    Lambda = K_BB - K_BI X.

No transpose, symmetrization, floating tolerance, condition-number threshold,
or pseudoinverse is part of C006.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias

RationalMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]


class InteriorNotAdmissibleError(ValueError):
    """Raised when the exact C006 interior system has no unique solution."""


def _validate_matrix(matrix: RationalMatrix, rows: int, cols: int, *, name: str) -> None:
    if type(matrix) is not tuple:
        raise TypeError(f"C006 {name} must be an immutable tuple of rows")
    if len(matrix) != rows:
        raise ValueError(f"C006 {name} row count mismatch")
    for row in matrix:
        if type(row) is not tuple:
            raise TypeError(f"C006 {name} rows must be immutable tuples")
        if len(row) != cols:
            raise ValueError(f"C006 {name} column count mismatch")
        if any(type(value) is not Fraction for value in row):
            raise TypeError(f"C006 {name} entries must be exact Fraction values")


def matrix_subtract(left: RationalMatrix, right: RationalMatrix) -> RationalMatrix:
    """Entrywise subtraction on equally shaped exact rational matrices."""
    if type(left) is not tuple or type(right) is not tuple or len(left) != len(right):
        raise ValueError("C006 matrix subtraction shape mismatch")
    out: list[tuple[Fraction, ...]] = []
    for lrow, rrow in zip(left, right, strict=True):
        if type(lrow) is not tuple or type(rrow) is not tuple or len(lrow) != len(rrow):
            raise ValueError("C006 matrix subtraction shape mismatch")
        if any(type(x) is not Fraction for x in lrow + rrow):
            raise TypeError("C006 matrix subtraction requires exact Fractions")
        out.append(tuple(a - b for a, b in zip(lrow, rrow, strict=True)))
    return tuple(out)


def matrix_multiply(left: RationalMatrix, right: RationalMatrix) -> RationalMatrix:
    """Row-by-column exact rational matrix product, with no transposition."""
    if type(left) is not tuple or type(right) is not tuple:
        raise TypeError("C006 matrix product requires immutable tuple matrices")
    left_rows = len(left)
    left_cols = len(left[0]) if left_rows else 0
    for row in left:
        if type(row) is not tuple or len(row) != left_cols:
            raise ValueError("C006 left matrix is not rectangular")
        if any(type(x) is not Fraction for x in row):
            raise TypeError("C006 matrix product requires exact Fractions")
    right_rows = len(right)
    right_cols = len(right[0]) if right_rows else 0
    for row in right:
        if type(row) is not tuple or len(row) != right_cols:
            raise ValueError("C006 right matrix is not rectangular")
        if any(type(x) is not Fraction for x in row):
            raise TypeError("C006 matrix product requires exact Fractions")
    if left_cols != right_rows:
        raise ValueError("C006 matrix product inner dimensions differ")
    if left_rows == 0:
        return ()
    if left_cols == 0:
        return tuple(tuple(Fraction(0, 1) for _ in range(right_cols)) for _ in range(left_rows))
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(left_cols)), Fraction(0, 1))
            for j in range(right_cols)
        )
        for i in range(left_rows)
    )


@dataclass(frozen=True, slots=True)
class OrderedSchurBlocks:
    """Exact C006 block data with inherited boundary/interior coordinate order."""

    k_bb: RationalMatrix
    k_bi: RationalMatrix
    k_ib: RationalMatrix
    k_ii: RationalMatrix

    def __post_init__(self) -> None:
        if type(self.k_bb) is not tuple or not self.k_bb:
            raise ValueError("C006 requires a nonempty boundary block K_BB")
        boundary = len(self.k_bb)
        interior = len(self.k_ii)
        _validate_matrix(self.k_bb, boundary, boundary, name="K_BB")
        _validate_matrix(self.k_bi, boundary, interior, name="K_BI")
        _validate_matrix(self.k_ib, interior, boundary, name="K_IB")
        _validate_matrix(self.k_ii, interior, interior, name="K_II")

    @property
    def boundary_size(self) -> int:
        return len(self.k_bb)

    @property
    def interior_size(self) -> int:
        return len(self.k_ii)


def is_interior_solve(blocks: OrderedSchurBlocks, solve: RationalMatrix) -> bool:
    """Common extensional solve predicate K_II X = K_IB."""
    if type(blocks) is not OrderedSchurBlocks:
        raise TypeError("C006 requires OrderedSchurBlocks")
    try:
        _validate_matrix(
            solve,
            blocks.interior_size,
            blocks.boundary_size,
            name="interior solve X",
        )
    except (TypeError, ValueError):
        return False
    return matrix_multiply(blocks.k_ii, solve) == blocks.k_ib


def _unique_interior_solve(blocks: OrderedSchurBlocks) -> RationalMatrix:
    """Exact Gauss-Jordan solve for K_II X = K_IB.

    A missing pivot means the square interior operator is singular, hence the
    requested solve is not unique.  No numerical tolerance is used.
    """
    n = blocks.interior_size
    m = blocks.boundary_size
    if n == 0:
        return ()

    augmented = [list(blocks.k_ii[i] + blocks.k_ib[i]) for i in range(n)]
    width = n + m
    for col in range(n):
        pivot_row = next((r for r in range(col, n) if augmented[r][col] != 0), None)
        if pivot_row is None:
            raise InteriorNotAdmissibleError(
                "C006 K_II does not admit a unique exact interior solve"
            )
        if pivot_row != col:
            augmented[col], augmented[pivot_row] = augmented[pivot_row], augmented[col]

        pivot = augmented[col][col]
        augmented[col] = [value / pivot for value in augmented[col]]
        for row in range(n):
            if row == col:
                continue
            factor = augmented[row][col]
            if factor == 0:
                continue
            augmented[row] = [
                augmented[row][j] - factor * augmented[col][j]
                for j in range(width)
            ]

    solve = tuple(tuple(augmented[i][n:]) for i in range(n))
    if not is_interior_solve(blocks, solve):
        raise AssertionError("C006 exact elimination failed its solve predicate")
    return solve


def interior_is_admissible(blocks: OrderedSchurBlocks) -> bool:
    """Exact C006 partial-domain predicate: the interior solve is unique."""
    if type(blocks) is not OrderedSchurBlocks:
        raise TypeError("C006 requires OrderedSchurBlocks")
    try:
        _unique_interior_solve(blocks)
    except InteriorNotAdmissibleError:
        return False
    return True


def schur_dtn_response_from_solve(
    blocks: OrderedSchurBlocks,
    solve: RationalMatrix,
) -> RationalMatrix:
    """Evaluate Lambda = K_BB - K_BI X for a supplied valid interior solve."""
    if type(blocks) is not OrderedSchurBlocks:
        raise TypeError("C006 requires OrderedSchurBlocks")
    if not is_interior_solve(blocks, solve):
        raise ValueError("C006 supplied X does not solve K_II X = K_IB")
    # Python's empty tuple cannot carry the column count of a 0 x b matrix.
    # The typed mathematical product K_BI (b x 0) X (0 x b) is the b x b
    # zero matrix, so the exact zero-interior Schur response is K_BB.
    if blocks.interior_size == 0:
        return blocks.k_bb
    correction = matrix_multiply(blocks.k_bi, solve)
    return matrix_subtract(blocks.k_bb, correction)


def schur_dtn_response(blocks: OrderedSchurBlocks) -> RationalMatrix:
    """Compute the unique exact C006 Schur/DtN response on its partial domain."""
    if type(blocks) is not OrderedSchurBlocks:
        raise TypeError("C006 requires OrderedSchurBlocks")
    solve = _unique_interior_solve(blocks)
    return schur_dtn_response_from_solve(blocks, solve)


__all__ = [
    "RationalMatrix",
    "InteriorNotAdmissibleError",
    "OrderedSchurBlocks",
    "matrix_subtract",
    "matrix_multiply",
    "is_interior_solve",
    "interior_is_admissible",
    "schur_dtn_response_from_solve",
    "schur_dtn_response",
]
