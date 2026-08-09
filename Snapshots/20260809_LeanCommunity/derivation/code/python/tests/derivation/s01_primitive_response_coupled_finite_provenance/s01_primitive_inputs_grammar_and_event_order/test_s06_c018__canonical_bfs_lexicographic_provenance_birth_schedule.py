"""Tests for Paper 1.1.6 / C018."""
from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import (
    CanonicalBirthSchedule,
    OpenBirthSlot,
    build_canonical_birth_schedule,
    canonical_birth_addresses,
    canonical_birth_slots,
    open_slot_key,
    slot_precedes,
)


class TestCanonicalBfsLexicographicSchedule(unittest.TestCase):
    def grammar(self, b: int, L: int):
        return build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
        )

    def test_exact_binary_depth_three_birth_order(self) -> None:
        g = self.grammar(2, 3)
        expected = (
            (0,), (1,),
            (0, 0), (0, 1), (1, 0), (1, 1),
            (0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1),
            (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
        )
        self.assertEqual(canonical_birth_addresses(g), expected)

    def test_parent_cursor_bfs_then_increasing_rank(self) -> None:
        g = self.grammar(3, 2)
        slots = canonical_birth_slots(g)
        self.assertEqual(
            tuple((s.parent, s.rank) for s in slots),
            (
                ((), 0), ((), 1), ((), 2),
                ((0,), 0), ((0,), 1), ((0,), 2),
                ((1,), 0), ((1,), 1), ((1,), 2),
                ((2,), 0), ((2,), 1), ((2,), 2),
            ),
        )
        self.assertEqual(tuple(s.child for s in slots), tuple(sorted((s.child for s in slots), key=lambda a: (len(a), a))))
        self.assertEqual(tuple(open_slot_key(s) for s in slots), tuple(sorted(open_slot_key(s) for s in slots)))

    def test_every_slot_is_one_word_extension_and_order_is_strict(self) -> None:
        slots = canonical_birth_slots(self.grammar(4, 2))
        for i, slot in enumerate(slots):
            with self.subTest(i=i, slot=slot):
                self.assertEqual(slot.child, slot.parent + (slot.rank,))
                self.assertFalse(slot_precedes(slot, slot))
                if i + 1 < len(slots):
                    self.assertTrue(slot_precedes(slot, slots[i + 1]))
                    self.assertFalse(slot_precedes(slots[i + 1], slot))

    def test_slot_order_is_strict_total_and_transitive(self) -> None:
        slots = canonical_birth_slots(self.grammar(3, 2))
        for left in slots:
            self.assertFalse(slot_precedes(left, left))
        for i, left in enumerate(slots):
            for j, right in enumerate(slots):
                if i == j:
                    continue
                lr = slot_precedes(left, right)
                rl = slot_precedes(right, left)
                self.assertNotEqual(lr, rl)
        for i in range(len(slots)):
            for j in range(i + 1, len(slots)):
                for k in range(j + 1, len(slots)):
                    self.assertTrue(slot_precedes(slots[i], slots[j]))
                    self.assertTrue(slot_precedes(slots[j], slots[k]))
                    self.assertTrue(slot_precedes(slots[i], slots[k]))

    def test_zero_cutoff_has_no_nonroot_birth_slots(self) -> None:
        g = self.grammar(5, 0)
        self.assertEqual(canonical_birth_slots(g), ())
        self.assertEqual(canonical_birth_addresses(g), ())
        self.assertEqual(build_canonical_birth_schedule(g).slots, ())

    def test_schedule_is_deterministic_and_has_only_c003_input(self) -> None:
        g = self.grammar(3, 3)
        s1 = build_canonical_birth_schedule(g)
        s2 = build_canonical_birth_schedule(g)
        self.assertEqual(s1, s2)
        self.assertEqual(s1.slots, s2.slots)
        self.assertEqual({f.name for f in dataclasses.fields(CanonicalBirthSchedule)}, {"grammar"})

    def test_no_event_index_time_geometry_response_or_layer_batch_state(self) -> None:
        schedule = build_canonical_birth_schedule(self.grammar(2, 2))
        forbidden = {
            "event_index", "event_id", "birth_time", "tau", "node_id", "nid",
            "position", "coordinates", "metric", "conductance", "response",
            "layer_batch", "batch", "batch_index",
        }
        self.assertTrue({f.name for f in dataclasses.fields(CanonicalBirthSchedule)}.isdisjoint(forbidden))
        self.assertTrue({f.name for f in dataclasses.fields(OpenBirthSlot)}.isdisjoint(forbidden))
        for name in forbidden:
            with self.subTest(name=name):
                self.assertFalse(hasattr(schedule, name))

    def test_invalid_predecessor_and_order_operands_are_rejected(self) -> None:
        with self.assertRaises(TypeError):
            build_canonical_birth_schedule(None)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            canonical_birth_slots(None)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            open_slot_key(((), 0, (0,)))  # type: ignore[arg-type]

    def test_schedule_cardinality_matches_full_bary_nonroot_carrier(self) -> None:
        for b in (2, 3, 4):
            for L in (0, 1, 2, 3):
                with self.subTest(b=b, L=L):
                    slots = canonical_birth_slots(self.grammar(b, L))
                    expected = sum(b**d for d in range(1, L + 1))
                    self.assertEqual(len(slots), expected)
                    self.assertEqual(len({slot.child for slot in slots}), expected)


if __name__ == "__main__":
    unittest.main()
