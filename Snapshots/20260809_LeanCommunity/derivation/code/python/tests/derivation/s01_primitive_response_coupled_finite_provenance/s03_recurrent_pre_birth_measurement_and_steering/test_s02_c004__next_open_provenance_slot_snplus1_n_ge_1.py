"""Focused tests for Paper 1.3.2 / C004."""
from __future__ import annotations

import unittest
from fractions import Fraction

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import is_next_open_provenance_slot, next_open_provenance_slot


def _state(b: int, L: int, n: int) -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
    )
    schedule = build_canonical_birth_schedule(grammar)
    born = schedule.addresses[:n]
    nodes = {grammar.root, *born}

    edges: list[DirectedConductance] = []
    for child in born:
        parent = grammar.parent(child)
        if parent not in nodes:
            raise AssertionError("test fixture violated provenance-parent closure")
        edges.append(DirectedConductance(parent, child, Fraction(1, 1)))
        edges.append(DirectedConductance(child, parent, Fraction(1, 1)))
    return ResponseCapableState(schedule, born, tuple(edges))


class TestNextOpenProvenanceSlot(unittest.TestCase):
    def test_indexed_successor_equals_unique_least_open_slot(self) -> None:
        # Exercise sibling continuation and the BFS transition to the next layer.
        for n, expected in (
            (1, (1,)),
            (2, (0, 0)),
            (3, (0, 1)),
            (4, (1, 0)),
        ):
            state = _state(2, 2, n)
            selected = next_open_provenance_slot(state)
            self.assertEqual(selected, state.schedule.slots[n])
            self.assertEqual(selected.child, expected)
            self.assertNotIn(selected.child, state.born_nonroot)
            self.assertIn(selected.parent, state.nodes)
            self.assertTrue(is_next_open_provenance_slot(state, selected))

            semantic_matches = tuple(
                slot
                for slot in state.schedule.slots
                if is_next_open_provenance_slot(state, slot)
            )
            self.assertEqual(semantic_matches, (selected,))

    def test_all_small_finite_prefixes_index_equals_extensional_object(self) -> None:
        # Cross-language semantic audit on an exhaustive finite grid.  Python's
        # positional constructor must identify exactly the unique least-open
        # C018 slot characterized relationally on the Lean side.
        for b in (2, 3, 4):
            for L in (1, 2, 3):
                grammar = build_finite_b_ary_provenance_grammar(
                    ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
                )
                schedule = build_canonical_birth_schedule(grammar)
                for n in range(1, len(schedule.slots)):
                    with self.subTest(b=b, L=L, n=n):
                        state = _state(b, L, n)
                        selected = next_open_provenance_slot(state)
                        self.assertEqual(selected, schedule.slots[n])
                        matches = tuple(
                            slot for slot in schedule.slots
                            if is_next_open_provenance_slot(state, slot)
                        )
                        self.assertEqual(matches, (selected,))
                        self.assertEqual(selected.child, selected.parent + (selected.rank,))

    def test_c018_order_not_incidental_tuple_position(self) -> None:
        state = _state(3, 2, 3)
        selected = next_open_provenance_slot(state)
        self.assertEqual(selected.child, (0, 0))
        self.assertEqual(selected.parent, (0,))
        self.assertEqual(selected.rank, 0)

        born = set(state.born_nonroot)
        for earlier in state.schedule.slots:
            if state.schedule.precedes(earlier, selected):
                self.assertIn(earlier.child, born)

    def test_saturation_has_no_sentinel(self) -> None:
        grammar = build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(1)
        )
        schedule = build_canonical_birth_schedule(grammar)
        saturated = _state(2, 1, len(schedule.slots))

        with self.assertRaises(LookupError):
            next_open_provenance_slot(saturated)

        semantic_matches = tuple(
            slot
            for slot in saturated.schedule.slots
            if is_next_open_provenance_slot(saturated, slot)
        )
        self.assertEqual(semantic_matches, ())


if __name__ == "__main__":
    unittest.main()
