"""Tests for Paper 1.1.2 / I002."""

from __future__ import annotations

import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import (
    FiniteApproximantDepth,
)


class TestFiniteApproximantDepth(unittest.TestCase):
    def test_zero_boundary_is_admitted(self) -> None:
        L = FiniteApproximantDepth(0)
        self.assertEqual(L.value, 0)
        self.assertEqual(L.to_int(), 0)

    def test_arbitrary_positive_integers_are_admitted(self) -> None:
        for value in (1, 2, 17, 101):
            with self.subTest(value=value):
                self.assertEqual(FiniteApproximantDepth(value).value, value)

    def test_negative_integers_are_rejected(self) -> None:
        for value in (-101, -3, -1):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    FiniteApproximantDepth(value)

    def test_non_integer_inputs_are_rejected(self) -> None:
        for value in (True, False, 0.0, "0", None):
            with self.subTest(value=value):
                with self.assertRaises(TypeError):
                    FiniteApproximantDepth(value)  # type: ignore[arg-type]


if __name__ == "__main__":
    unittest.main()
