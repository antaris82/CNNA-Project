"""Tests for Paper 1.2.1 / C004A."""
from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule, slot_precedes
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s01_c004a__first_provenance_slot_s1 import (
    FirstProvenanceSlot,
    build_canonical_first_provenance_slot,
    build_first_provenance_slot,
)


class TestFirstProvenanceSlot(unittest.TestCase):
    def grammar(self, b: int, L: int):
        return build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
        )

    def test_s1_is_root_rank_zero_and_address_zero(self) -> None:
        for b in (2, 3, 5):
            for L in (0, 1, 3):
                with self.subTest(b=b, L=L):
                    s1 = build_canonical_first_provenance_slot(self.grammar(b, L))
                    self.assertEqual(s1.parent, ())
                    self.assertEqual(s1.rank, 0)
                    self.assertEqual(s1.address, (0,))

    def test_one_based_name_does_not_shift_zero_based_rank(self) -> None:
        s1 = build_canonical_first_provenance_slot(self.grammar(4, 2))
        self.assertEqual(s1.rank, 0)
        self.assertNotEqual(s1.rank, 1)

    def test_c018_selects_s1_as_first_admitted_slot_when_L_positive(self) -> None:
        for b in (2, 3, 4):
            for L in (1, 2, 3):
                with self.subTest(b=b, L=L):
                    g = self.grammar(b, L)
                    s1 = build_canonical_first_provenance_slot(g)
                    slots = s1.schedule.slots
                    self.assertGreater(len(slots), 0)
                    self.assertEqual(slots[0].parent, s1.parent)
                    self.assertEqual(slots[0].rank, s1.rank)
                    self.assertEqual(slots[0].child, s1.address)
                    for later in slots[1:]:
                        self.assertTrue(slot_precedes(slots[0], later))
                        self.assertFalse(slot_precedes(later, slots[0]))

    def test_L_zero_retains_structural_slot_but_admits_no_birth_slot(self) -> None:
        s1 = build_canonical_first_provenance_slot(self.grammar(3, 0))
        self.assertEqual(s1.address, (0,))
        self.assertFalse(s1.admitted_by_cutoff)
        self.assertEqual(s1.schedule.slots, ())
        with self.assertRaises(ValueError):
            s1.require_admitted_address()

    def test_positive_cutoff_admits_s1_without_performing_birth(self) -> None:
        for L in (1, 2, 5):
            with self.subTest(L=L):
                s1 = build_canonical_first_provenance_slot(self.grammar(2, L))
                self.assertTrue(s1.admitted_by_cutoff)
                self.assertEqual(s1.require_admitted_address(), (0,))

    def test_two_direct_predecessors_must_share_same_grammar(self) -> None:
        g1 = self.grammar(2, 2)
        g2 = self.grammar(3, 2)
        schedule2 = build_canonical_birth_schedule(g2)
        with self.assertRaises(ValueError):
            build_first_provenance_slot(g1, schedule2)

    def test_invalid_predecessor_types_are_rejected(self) -> None:
        g = self.grammar(2, 1)
        schedule = build_canonical_birth_schedule(g)
        with self.assertRaises(TypeError):
            build_first_provenance_slot(None, schedule)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            build_first_provenance_slot(g, None)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            build_canonical_first_provenance_slot(None)  # type: ignore[arg-type]

    def test_payload_contains_only_direct_predecessors(self) -> None:
        s1 = build_canonical_first_provenance_slot(self.grammar(2, 2))
        self.assertEqual(
            {f.name for f in dataclasses.fields(FirstProvenanceSlot)},
            {"grammar", "schedule"},
        )
        forbidden = {
            "position", "coordinates", "metric", "geometry",
            "node_id", "nid", "event_index", "birth_time", "tau",
            "conductance", "response", "birth_g", "g",
        }
        self.assertTrue({f.name for f in dataclasses.fields(FirstProvenanceSlot)}.isdisjoint(forbidden))
        for name in forbidden:
            with self.subTest(name=name):
                self.assertFalse(hasattr(s1, name))


if __name__ == "__main__":
    unittest.main()
