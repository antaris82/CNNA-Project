"""Tests for Paper 1.2.2 / A001."""
from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s02_a001__genesis_seed_star import (
    GENESIS_SEED,
    GenesisSeed,
)


class TestGenesisSeed(unittest.TestCase):
    def test_seed_has_one_payload_free_value(self) -> None:
        self.assertEqual(dataclasses.fields(GenesisSeed), ())
        self.assertEqual(GenesisSeed(), GENESIS_SEED)

    def test_seed_carries_no_bootstrap_result_data(self) -> None:
        for name in (
            "value", "parent", "child", "relation", "conductance", "address",
            "birth_time", "event_index", "geometry", "response",
        ):
            with self.subTest(name=name):
                self.assertFalse(hasattr(GENESIS_SEED, name))


if __name__ == "__main__":
    unittest.main()
