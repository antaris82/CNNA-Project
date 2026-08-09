"""Tests for Paper 1.2.3 / N001."""
from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import (
    C_STAR,
    INITIAL_CONDUCTANCE_NORMALIZATION,
    InitialConductanceNormalization,
)


class TestInitialConductanceNormalization(unittest.TestCase):
    def test_unit_value_and_directed_symmetry(self) -> None:
        n = INITIAL_CONDUCTANCE_NORMALIZATION
        self.assertEqual(C_STAR, 1)
        self.assertEqual(n.value, 1)
        self.assertEqual(n.directed_values, (1, 1))

    def test_fixed_normalization_has_no_free_or_birth_payload(self) -> None:
        n = INITIAL_CONDUCTANCE_NORMALIZATION
        self.assertEqual(dataclasses.fields(InitialConductanceNormalization), ())
        self.assertEqual(InitialConductanceNormalization(), n)
        with self.assertRaises(TypeError):
            InitialConductanceNormalization(2)  # type: ignore[call-arg]
        for name in ("parent", "child", "relation", "node", "address", "birth_time", "event_index"):
            with self.subTest(name=name):
                self.assertFalse(hasattr(n, name))


if __name__ == "__main__":
    unittest.main()
