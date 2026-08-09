"""Focused tests for Paper 1.3.8 / C015."""
from __future__ import annotations

import inspect
import unittest
from fractions import Fraction

import cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s08_c015__active_linear_steering_mode_phi_x_x as c015
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s08_c015__active_linear_steering_mode_phi_x_x import (
    active_linear_steering,
)


class TestActivePathIdentityTransform(unittest.TestCase):
    def test_identity_on_exact_fraction_scalars(self) -> None:
        values = (
            Fraction(0, 1),
            Fraction(1, 3),
            Fraction(-5, 7),
            Fraction(29, 11),
        )
        self.assertEqual(tuple(active_linear_steering(x) for x in values), values)

    def test_preserves_the_exact_input_object_without_coercion(self) -> None:
        marker = object()
        self.assertIs(active_linear_steering(marker), marker)
        fraction = Fraction(2, 9)
        self.assertIs(active_linear_steering(fraction), fraction)

    def test_active_api_has_one_positional_only_argument(self) -> None:
        signature = inspect.signature(active_linear_steering)
        parameters = tuple(signature.parameters.values())
        self.assertEqual(len(parameters), 1)
        self.assertEqual(parameters[0].name, "response_scalar")
        self.assertIs(parameters[0].kind, inspect.Parameter.POSITIONAL_ONLY)

    def test_no_mode_or_scale_object_is_exported(self) -> None:
        self.assertEqual(tuple(c015.__all__), ("active_linear_steering",))
        self.assertFalse(hasattr(c015, "ActiveSteeringMode"))
        self.assertFalse(hasattr(c015, "ACTIVE_STEERING_MODE"))
        signature = inspect.signature(active_linear_steering)
        for forbidden in ("mode", "scale", "slope", "coefficient"):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, signature.parameters)

    def test_public_api_contains_no_control_transform(self) -> None:
        exported = " ".join(c015.__all__).lower()
        for forbidden in ("log", "saturat", "sym", "null"):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, exported)


if __name__ == "__main__":
    unittest.main()
