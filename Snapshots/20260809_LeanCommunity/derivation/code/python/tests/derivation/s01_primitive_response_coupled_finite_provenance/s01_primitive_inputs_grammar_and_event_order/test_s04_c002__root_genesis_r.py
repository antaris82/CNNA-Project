"""Tests for Paper 1.1.4 / C002."""

from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s03_c001__empty_carrier_empty import (
    EMPTY_CARRIER,
    EmptyCarrier,
)
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import (
    ROOT,
    ROOTED_CARRIER,
    Root,
    RootedCarrier,
    root_genesis,
)


class TestRootGenesis(unittest.TestCase):
    def test_genesis_creates_exactly_one_root_and_no_relation(self) -> None:
        state = root_genesis(EMPTY_CARRIER)
        self.assertIs(state, ROOTED_CARRIER)
        self.assertEqual(state.nodes, (ROOT,))
        self.assertEqual(len(state.nodes), 1)
        self.assertEqual(state.relations, ())
        self.assertFalse(state.contains_relation(ROOT, ROOT))

    def test_root_is_unique_zero_payload_and_has_no_parent(self) -> None:
        self.assertEqual(dataclasses.fields(Root), ())
        self.assertEqual(dataclasses.fields(RootedCarrier), ())
        self.assertFalse(hasattr(ROOT, "__dict__"))
        self.assertFalse(hasattr(ROOTED_CARRIER, "__dict__"))
        self.assertEqual(Root(), ROOT)
        self.assertEqual(RootedCarrier(), ROOTED_CARRIER)
        self.assertTrue(ROOTED_CARRIER.contains_node(ROOT))
        self.assertIsNone(ROOTED_CARRIER.parent_of(ROOT))

    def test_c002_does_not_smuggle_downstream_metadata(self) -> None:
        forbidden = (
            "address",
            "nid",
            "node_id",
            "level",
            "depth",
            "sibling_rank",
            "birth_time",
            "event_index",
            "g",
            "birth_g",
            "conductance",
            "response",
            "position",
            "coordinates",
        )
        for name in forbidden:
            with self.subTest(name=name):
                self.assertFalse(hasattr(ROOT, name))
                self.assertFalse(hasattr(ROOTED_CARRIER, name))

    def test_genesis_domain_is_exactly_empty_carrier(self) -> None:
        self.assertIs(root_genesis(EmptyCarrier()), ROOTED_CARRIER)
        for invalid in (None, ROOT, ROOTED_CARRIER, (), object()):
            with self.subTest(invalid=invalid):
                with self.assertRaises(TypeError):
                    root_genesis(invalid)  # type: ignore[arg-type]


if __name__ == "__main__":
    unittest.main()
