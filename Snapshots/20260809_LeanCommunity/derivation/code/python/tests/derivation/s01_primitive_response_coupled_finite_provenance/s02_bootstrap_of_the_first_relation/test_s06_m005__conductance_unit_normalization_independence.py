"""Focused executable check for Paper 1.2.6 / M005."""
from __future__ import annotations

from fractions import Fraction
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import INITIAL_CONDUCTANCE_NORMALIZATION
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s06_m005__conductance_unit_normalization_independence import (
    common_positive_rescaling_preserves_normalized_response,
    n001_normalized_response,
)


class TestConductanceUnitNormalizationIndependence(unittest.TestCase):
    def test_common_positive_rescaling_changes_units_not_normalized_response(self) -> None:
        for response, scale in ((3, 2), (-5, 7), (Fraction(2, 3), Fraction(1, 3))):
            with self.subTest(response=response, scale=scale):
                self.assertTrue(
                    common_positive_rescaling_preserves_normalized_response(
                        response,
                        INITIAL_CONDUCTANCE_NORMALIZATION.value,
                        scale,
                    )
                )
                self.assertEqual(n001_normalized_response(response, INITIAL_CONDUCTANCE_NORMALIZATION), Fraction(response))


if __name__ == "__main__":
    unittest.main()
