"""Focused tests for Paper 1.3.3 / C006."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s03_c006__birth_local_schur_dtn_primitive import (
    InteriorNotAdmissibleError,
    OrderedSchurBlocks,
    interior_is_admissible,
    is_interior_solve,
    matrix_multiply,
    schur_dtn_response,
    schur_dtn_response_from_solve,
)


def _raw_of_fraction(value: F, scale: int) -> tuple[int, int]:
    if scale <= 0:
        raise ValueError("scale must be positive")
    return value.numerator * scale, value.denominator * scale


def _raw_value(raw: tuple[int, int]) -> F:
    numerator, denominator = raw
    return F(numerator, denominator)


def _raw_add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    ln, ld = left
    rn, rd = right
    return ln * rd + rn * ld, ld * rd


def _raw_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    ln, ld = left
    rn, rd = right
    return ln * rn, ld * rd


def _raw_sub(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    ln, ld = left
    rn, rd = right
    return ln * rd - rn * ld, ld * rd


class TestBirthLocalSchurDtnPrimitive(unittest.TestCase):
    def test_exact_nonsymmetric_one_dimensional_interior(self) -> None:
        blocks = OrderedSchurBlocks(
            k_bb=((F(4), F(7)), (F(2), F(5))),
            k_bi=((F(1),), (F(3),)),
            k_ib=((F(2), F(4)),),
            k_ii=((F(2),),),
        )
        self.assertTrue(interior_is_admissible(blocks))
        self.assertEqual(
            schur_dtn_response(blocks),
            ((F(3), F(5)), (F(-1), F(-1))),
        )
        # C006 must not symmetrize a directed/non-symmetric input.
        self.assertNotEqual(
            schur_dtn_response(blocks)[0][1],
            schur_dtn_response(blocks)[1][0],
        )

    def test_exact_two_dimensional_interior_and_explicit_solve_predicate(self) -> None:
        blocks = OrderedSchurBlocks(
            k_bb=((F(10),),),
            k_bi=((F(2), F(1)),),
            k_ib=((F(3),), (F(5),)),
            k_ii=((F(2), F(1)), (F(1), F(1))),
        )
        solve = ((F(-2),), (F(7),))
        self.assertTrue(is_interior_solve(blocks, solve))
        self.assertEqual(matrix_multiply(blocks.k_ii, solve), blocks.k_ib)
        self.assertEqual(schur_dtn_response_from_solve(blocks, solve), ((F(7),),))
        self.assertEqual(schur_dtn_response(blocks), ((F(7),),))

    def test_zero_interior_is_total_and_returns_kbb_exactly(self) -> None:
        blocks = OrderedSchurBlocks(
            k_bb=((F(2), F(-3)), (F(5), F(11))),
            k_bi=((), ()),
            k_ib=(),
            k_ii=(),
        )
        self.assertTrue(interior_is_admissible(blocks))
        self.assertTrue(is_interior_solve(blocks, ()))
        self.assertEqual(schur_dtn_response(blocks), blocks.k_bb)

    def test_singular_interior_is_rejected_exactly_without_tolerance(self) -> None:
        blocks = OrderedSchurBlocks(
            k_bb=((F(1),),),
            k_bi=((F(1), F(0)),),
            k_ib=((F(1),), (F(2),)),
            k_ii=((F(1), F(2)), (F(2), F(4))),
        )
        self.assertFalse(interior_is_admissible(blocks))
        with self.assertRaises(InteriorNotAdmissibleError):
            schur_dtn_response(blocks)

    def test_block_shapes_and_exact_scalar_carrier_are_locked(self) -> None:
        with self.assertRaises(ValueError):
            OrderedSchurBlocks(
                k_bb=(),
                k_bi=(),
                k_ib=(),
                k_ii=(),
            )
        with self.assertRaises(ValueError):
            OrderedSchurBlocks(
                k_bb=((F(1),),),
                k_bi=((F(1),),),
                k_ib=(),
                k_ii=(),
            )
        with self.assertRaises(TypeError):
            OrderedSchurBlocks(
                k_bb=((1,),),  # type: ignore[arg-type]
                k_bi=((),),
                k_ib=(),
                k_ii=(),
            )

    def test_exact_domain_matches_two_by_two_determinant_on_small_grid(self) -> None:
        values = (F(-1), F(0), F(1))
        for a in values:
            for b in values:
                for c in values:
                    for d in values:
                        with self.subTest(k_ii=(a, b, c, d)):
                            blocks = OrderedSchurBlocks(
                                k_bb=((F(2),),),
                                k_bi=((F(1), F(3)),),
                                k_ib=((F(1),), (F(-2),)),
                                k_ii=((a, b), (c, d)),
                            )
                            determinant_nonzero = a * d - b * c != 0
                            self.assertEqual(
                                interior_is_admissible(blocks),
                                determinant_nonzero,
                            )
                            if determinant_nonzero:
                                response = schur_dtn_response(blocks)
                                self.assertEqual(len(response), 1)
                                self.assertEqual(len(response[0]), 1)

    def test_invalid_explicit_solve_cannot_define_a_response(self) -> None:
        blocks = OrderedSchurBlocks(
            k_bb=((F(3),),),
            k_bi=((F(2),),),
            k_ib=((F(5),),),
            k_ii=((F(4),),),
        )
        bad = ((F(1),),)
        self.assertFalse(is_interior_solve(blocks, bad))
        with self.assertRaises(ValueError):
            schur_dtn_response_from_solve(blocks, bad)

    def test_raw_fraction_operations_preserve_exact_rational_values(self) -> None:
        values = (F(-7, 5), F(-1, 3), F(0), F(2, 7), F(11, 4))
        scales = (1, 2, 5)
        for left in values:
            for right in values:
                for left_scale in scales:
                    for right_scale in scales:
                        with self.subTest(
                            left=left,
                            right=right,
                            left_scale=left_scale,
                            right_scale=right_scale,
                        ):
                            raw_left = _raw_of_fraction(left, left_scale)
                            raw_right = _raw_of_fraction(right, right_scale)
                            self.assertEqual(_raw_value(_raw_add(raw_left, raw_right)), left + right)
                            self.assertEqual(_raw_value(_raw_mul(raw_left, raw_right)), left * right)
                            self.assertEqual(_raw_value(_raw_sub(raw_left, raw_right)), left - right)

    def test_raw_matrix_product_matches_fraction_matrix_product(self) -> None:
        left = ((F(2, 3), F(-5, 7)), (F(11, 4), F(1, 6)))
        right = ((F(3, 5), F(7, 2)), (F(-2, 9), F(5, 8)))
        left_scales = ((2, 3), (5, 7))
        right_scales = ((11, 13), (17, 19))
        raw_left = tuple(
            tuple(_raw_of_fraction(left[i][j], left_scales[i][j]) for j in range(2))
            for i in range(2)
        )
        raw_right = tuple(
            tuple(_raw_of_fraction(right[i][j], right_scales[i][j]) for j in range(2))
            for i in range(2)
        )
        raw_product = tuple(
            tuple(
                _raw_add(
                    _raw_mul(raw_left[i][0], raw_right[0][j]),
                    _raw_mul(raw_left[i][1], raw_right[1][j]),
                )
                for j in range(2)
            )
            for i in range(2)
        )
        self.assertEqual(
            tuple(tuple(_raw_value(entry) for entry in row) for row in raw_product),
            matrix_multiply(left, right),
        )


if __name__ == "__main__":
    unittest.main()
