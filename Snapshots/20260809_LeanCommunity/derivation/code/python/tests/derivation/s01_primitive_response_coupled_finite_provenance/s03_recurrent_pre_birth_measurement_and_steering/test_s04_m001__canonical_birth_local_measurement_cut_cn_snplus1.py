"""Focused tests for Paper 1.3.4 / M001."""
from __future__ import annotations

import unittest
from fractions import Fraction

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import next_open_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s04_m001__canonical_birth_local_measurement_cut_cn_snplus1 import (
    canonical_birth_local_measurement_cut,
    causal_predecessor_ports,
    is_birth_local_port,
    is_canonical_birth_local_measurement_cut,
    older_sibling_ports,
)


def _state(b: int, L: int, n: int, scale: Fraction = Fraction(1, 1)) -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
    )
    schedule = build_canonical_birth_schedule(grammar)
    born = schedule.addresses[:n]
    edges: list[DirectedConductance] = []
    for idx, child in enumerate(born, start=1):
        parent = grammar.parent(child)
        forward = scale * Fraction(idx + 1, idx)
        backward = scale * Fraction(idx + 2, idx + 1)
        edges.append(DirectedConductance(parent, child, forward))
        edges.append(DirectedConductance(child, parent, backward))
    return ResponseCapableState(schedule, born, tuple(edges))


class TestCanonicalBirthLocalMeasurementCut(unittest.TestCase):
    def test_exact_birth_local_roles_and_order(self) -> None:
        cases = (
            # X1: next root sibling. Root and the first child are the two ports.
            (2, 2, 1, ((), (0,)), ()),
            # First child of (0): retain root->(0); the other root child is interior.
            (2, 2, 2, ((), (0,)), ((1,),)),
            # Second child of (0): its older sibling becomes an explicit port.
            (2, 2, 3, ((), (0,), (0, 0)), ((1,),)),
            # First grandchild of (0,0): full root-to-parent chain is retained.
            (2, 3, 6, ((), (0,), (0, 0)), ((1,), (0, 1), (1, 0), (1, 1))),
        )
        for b, L, n, expected_boundary, expected_interior in cases:
            with self.subTest(b=b, L=L, n=n):
                state = _state(b, L, n)
                slot = next_open_provenance_slot(state)
                cut = canonical_birth_local_measurement_cut(state, slot)
                self.assertEqual(cut.boundary, expected_boundary)
                self.assertEqual(cut.interior, expected_interior)
                self.assertEqual(causal_predecessor_ports(slot), tuple(slot.parent[:d] for d in range(len(slot.parent) + 1)))
                self.assertEqual(older_sibling_ports(slot), tuple(slot.parent + (r,) for r in range(slot.rank)))
                self.assertTrue(is_canonical_birth_local_measurement_cut(state, slot, cut))
                self.assertNotIn(slot.child, cut.boundary)
                self.assertNotIn(slot.child, cut.interior)

    def test_every_finite_prefix_is_exact_partition_with_no_caps(self) -> None:
        for b, L in ((2, 2), (2, 3), (3, 2), (3, 3), (4, 2)):
            grammar = build_finite_b_ary_provenance_grammar(
                ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
            )
            schedule = build_canonical_birth_schedule(grammar)
            for n in range(1, len(schedule.slots)):
                with self.subTest(b=b, L=L, n=n):
                    state = _state(b, L, n)
                    slot = next_open_provenance_slot(state)
                    cut = canonical_birth_local_measurement_cut(state)
                    expected_boundary = tuple(a for a in state.nodes if is_birth_local_port(slot, a))
                    expected_interior = tuple(a for a in state.nodes if not is_birth_local_port(slot, a))
                    self.assertEqual(cut.boundary, expected_boundary)
                    self.assertEqual(cut.interior, expected_interior)
                    self.assertEqual(set(cut.boundary) | set(cut.interior), set(state.nodes))
                    self.assertFalse(set(cut.boundary) & set(cut.interior))
                    self.assertIn(state.root, cut.boundary)
                    self.assertIn(slot.parent, cut.boundary)

    def test_cut_is_provenance_only_and_rejects_non_c004_slot(self) -> None:
        state_a = _state(3, 2, 4, Fraction(1, 1))
        state_b = _state(3, 2, 4, Fraction(7, 5))
        slot = next_open_provenance_slot(state_a)
        self.assertEqual(slot, next_open_provenance_slot(state_b))
        self.assertEqual(
            canonical_birth_local_measurement_cut(state_a, slot),
            canonical_birth_local_measurement_cut(state_b, slot),
        )

        later_slot = state_a.schedule.slots[state_a.n + 1]
        with self.assertRaises(ValueError):
            canonical_birth_local_measurement_cut(state_a, later_slot)


if __name__ == "__main__":
    unittest.main()
