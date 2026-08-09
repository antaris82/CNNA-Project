"""Tests for Paper 1.1.1 / I001."""

from __future__ import annotations

import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import (
    BranchingParameter,
)


class TestBranchingParameter(unittest.TestCase):
    def test_lower_boundary_is_admitted(self) -> None:
        b = BranchingParameter(2)
        self.assertEqual(b.value, 2)
        self.assertEqual(b.to_int(), 2)

    def test_arbitrary_larger_integers_are_admitted(self) -> None:
        for value in (3, 4, 17, 101):
            with self.subTest(value=value):
                self.assertEqual(BranchingParameter(value).value, value)

    def test_values_below_two_are_rejected(self) -> None:
        for value in (-3, -1, 0, 1):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    BranchingParameter(value)

    def test_non_integer_inputs_are_rejected(self) -> None:
        for value in (True, False, 2.0, "2", None):
            with self.subTest(value=value):
                with self.assertRaises(TypeError):
                    BranchingParameter(value)  # type: ignore[arg-type]


if __name__ == "__main__":
    unittest.main()
