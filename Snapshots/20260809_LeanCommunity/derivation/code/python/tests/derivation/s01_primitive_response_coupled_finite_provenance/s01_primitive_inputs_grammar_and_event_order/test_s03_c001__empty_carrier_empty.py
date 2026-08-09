"""Tests for Paper 1.1.3 / C001."""

from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s03_c001__empty_carrier_empty import (
    EMPTY_CARRIER,
    EmptyCarrier,
)


class TestEmptyCarrier(unittest.TestCase):
    def test_canonical_carrier_has_no_nodes_or_relations(self) -> None:
        self.assertEqual(EMPTY_CARRIER.nodes, ())
        self.assertEqual(EMPTY_CARRIER.relations, ())
        self.assertEqual(len(EMPTY_CARRIER.nodes), 0)
        self.assertEqual(len(EMPTY_CARRIER.relations), 0)

    def test_membership_and_relation_queries_are_vacuous(self) -> None:
        probes = (None, 0, (), "root", object())
        for probe in probes:
            with self.subTest(node=probe):
                self.assertFalse(EMPTY_CARRIER.contains_node(probe))
        for source in probes:
            for target in probes:
                with self.subTest(source=source, target=target):
                    self.assertFalse(EMPTY_CARRIER.contains_relation(source, target))

    def test_carrier_has_no_stored_payload_fields(self) -> None:
        self.assertEqual(dataclasses.fields(EmptyCarrier), ())
        self.assertFalse(hasattr(EMPTY_CARRIER, "__dict__"))

    def test_all_constructed_values_are_the_same_empty_value_semantically(self) -> None:
        self.assertEqual(EmptyCarrier(), EMPTY_CARRIER)
        with self.assertRaises(TypeError):
            EmptyCarrier("hidden payload")  # type: ignore[call-arg]


if __name__ == "__main__":
    unittest.main()
