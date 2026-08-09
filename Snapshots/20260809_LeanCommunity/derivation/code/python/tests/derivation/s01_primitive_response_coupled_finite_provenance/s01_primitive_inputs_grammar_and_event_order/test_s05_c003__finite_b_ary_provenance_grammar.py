"""Tests for Paper 1.1.5 / C003."""

from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOT, ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import (
    FiniteBAryProvenanceGrammar,
    address_depth,
    address_parent,
    build_finite_b_ary_provenance_grammar,
    child_address,
    final_slot,
    is_parent_of,
    root_address,
    slot_alphabet,
    validate_unbounded_address,
)


class TestFiniteBAryProvenanceGrammar(unittest.TestCase):
    def setUp(self) -> None:
        self.b = BranchingParameter(3)
        self.L = FiniteApproximantDepth(2)
        self.grammar = build_finite_b_ary_provenance_grammar(ROOTED_CARRIER, self.b, self.L)

    def test_three_predecessors_join_and_root_is_anchored_to_empty_word(self) -> None:
        self.assertIs(self.grammar.rooted_carrier, ROOTED_CARRIER)
        self.assertIs(self.grammar.branching, self.b)
        self.assertIs(self.grammar.cutoff, self.L)
        self.assertEqual(self.grammar.root_address_for(ROOT), ())
        self.assertEqual(self.grammar.root, ())
        self.assertEqual(root_address(), ())
        self.assertEqual(self.grammar.depth(()), 0)

    def test_slot_alphabet_is_exactly_zero_through_b_minus_one(self) -> None:
        self.assertEqual(slot_alphabet(self.b), (0, 1, 2))
        self.assertEqual(self.grammar.slots, (0, 1, 2))
        for b_value in (2, 3, 5):
            with self.subTest(b=b_value):
                b = BranchingParameter(b_value)
                self.assertEqual(slot_alphabet(b), tuple(range(b_value)))

    def test_child_parent_rank_and_depth_are_word_derived(self) -> None:
        u = self.grammar.child((), 2)
        a = self.grammar.child(u, 1)
        self.assertEqual(u, (2,))
        self.assertEqual(a, (2, 1))
        self.assertEqual(self.grammar.parent(a), u)
        self.assertEqual(self.grammar.rank(a), 1)
        self.assertEqual(self.grammar.depth(a), 2)
        self.assertEqual(address_parent(self.b, a), u)
        self.assertEqual(final_slot(self.b, a), 1)
        self.assertEqual(address_depth(self.b, a), 2)
        self.assertTrue(self.grammar.parent_relation(u, a))
        self.assertTrue(is_parent_of(self.b, u, a))
        self.assertFalse(is_parent_of(self.b, (), a))

    def test_local_b_ary_word_constructor_is_independent_of_cutoff(self) -> None:
        a = child_address(self.b, (2, 1), 0)
        self.assertEqual(a, (2, 1, 0))
        self.assertEqual(validate_unbounded_address(self.b, a), a)
        with self.assertRaises(ValueError):
            self.grammar.validate_address(a)
        with self.assertRaises(ValueError):
            self.grammar.child((2, 1), 0)

    def test_zero_cutoff_is_root_only_for_admitted_words(self) -> None:
        g = build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(4), FiniteApproximantDepth(0)
        )
        self.assertEqual(g.root, ())
        self.assertEqual(g.validate_address(()), ())
        with self.assertRaises(ValueError):
            g.validate_address((0,))
        with self.assertRaises(ValueError):
            g.child((), 0)
        self.assertEqual(slot_alphabet(g.branching), (0, 1, 2, 3))
        self.assertEqual(child_address(g.branching, (), 3), (3,))

    def test_root_has_no_parent_or_final_rank(self) -> None:
        with self.assertRaises(ValueError):
            self.grammar.parent(())
        with self.assertRaises(ValueError):
            self.grammar.rank(())

    def test_invalid_ranks_addresses_and_predecessor_types_are_rejected(self) -> None:
        for bad_rank in (-1, 3):
            with self.subTest(bad_rank=bad_rank):
                with self.assertRaises(ValueError):
                    child_address(self.b, (), bad_rank)
        for bad_rank in (True, 1.0, "1", None):
            with self.subTest(bad_rank=bad_rank):
                with self.assertRaises(TypeError):
                    child_address(self.b, (), bad_rank)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            validate_unbounded_address(self.b, [0, 1])  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            validate_unbounded_address(self.b, (0, 3))
        with self.assertRaises(TypeError):
            build_finite_b_ary_provenance_grammar(None, self.b, self.L)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            build_finite_b_ary_provenance_grammar(ROOTED_CARRIER, 3, self.L)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            build_finite_b_ary_provenance_grammar(ROOTED_CARRIER, self.b, 2)  # type: ignore[arg-type]

    def test_c003_adds_no_event_geometry_response_or_node_id_fields(self) -> None:
        field_names = {field.name for field in dataclasses.fields(FiniteBAryProvenanceGrammar)}
        self.assertEqual(field_names, {"rooted_carrier", "branching", "cutoff"})
        forbidden = {
            "event_id", "birth_time", "linearization_index", "node_id", "nid",
            "position", "coordinates", "conductance", "response", "g", "birth_g",
            "growth_schedule", "sibling_linearization",
        }
        self.assertTrue(field_names.isdisjoint(forbidden))
        for name in forbidden:
            with self.subTest(name=name):
                self.assertFalse(hasattr(self.grammar, name))


if __name__ == "__main__":
    unittest.main()
