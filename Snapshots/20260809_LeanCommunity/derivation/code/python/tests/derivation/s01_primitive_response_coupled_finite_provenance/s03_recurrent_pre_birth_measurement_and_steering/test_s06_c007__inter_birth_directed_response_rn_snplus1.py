"""Focused tests for Paper 1.3.6 / C007."""
from __future__ import annotations

import unittest
from fractions import Fraction

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s01_c004a__first_provenance_slot_s1 import build_canonical_first_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s02_a001__genesis_seed_star import GENESIS_SEED
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import INITIAL_CONDUCTANCE_NORMALIZATION
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s04_c013__first_non_root_provenance_birth_v1 import build_first_non_root_birth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import build_bootstrap_state
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import (
    DirectedConductance,
    ResponseCapableState,
    response_capable_state_from_bootstrap,
)
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import next_open_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s05_m002__birth_cut_interior_domain_theorem import birth_cut_interior_is_admissible
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s06_c007__inter_birth_directed_response_rn_snplus1 import (
    MATRIX_CONVENTION,
    inter_birth_directed_response,
    state_directed_schur_realization,
)


def _bootstrap_state() -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(2)
    )
    slot = build_canonical_first_provenance_slot(grammar)
    birth = build_first_non_root_birth(slot, GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
    return response_capable_state_from_bootstrap(build_bootstrap_state(birth))


def _state(b: int, L: int, n: int, scale: Fraction = Fraction(1, 1), *, extra: bool = False) -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
    )
    schedule = build_canonical_birth_schedule(grammar)
    born = schedule.addresses[:n]
    edges: list[DirectedConductance] = []
    for idx, child in enumerate(born, start=1):
        parent = grammar.parent(child)
        edges.append(DirectedConductance(parent, child, scale * Fraction(idx + 1, idx)))
        edges.append(DirectedConductance(child, parent, scale * Fraction(idx + 2, idx + 1)))
    if extra and len(born) >= 2:
        left, right = born[0], born[1]
        edges.append(DirectedConductance(left, right, scale * Fraction(5, 7)))
        edges.append(DirectedConductance(right, left, scale * Fraction(7, 11)))
    return ResponseCapableState(schedule, born, tuple(edges))


class TestInterBirthDirectedResponse(unittest.TestCase):
    def test_bootstrap_response_is_full_two_node_directed_laplacian(self) -> None:
        state = _bootstrap_state()
        result = inter_birth_directed_response(state)
        self.assertEqual(MATRIX_CONVENTION, "source_out_degree_closed_current_carrier")
        self.assertEqual(result.birth_count, 1)
        self.assertEqual(result.slot.child, (1,))
        self.assertEqual(result.boundary, ((), (0,)))
        self.assertEqual(result.realization.cut.interior, ())
        self.assertEqual(
            result.value,
            (
                (Fraction(1, 1), Fraction(-1, 1)),
                (Fraction(-1, 1), Fraction(1, 1)),
            ),
        )

    def test_asymmetric_out_degree_block_assembly_and_schur_value(self) -> None:
        state = _state(2, 2, 2)
        realization = state_directed_schur_realization(state)
        self.assertEqual(realization.slot.child, (0, 0))
        self.assertEqual(realization.cut.boundary, ((), (0,)))
        self.assertEqual(realization.cut.interior, ((1,),))
        self.assertEqual(
            realization.full_matrix,
            (
                (Fraction(7, 2), Fraction(-2, 1), Fraction(-3, 2)),
                (Fraction(-3, 2), Fraction(3, 2), Fraction(0, 1)),
                (Fraction(-4, 3), Fraction(0, 1), Fraction(4, 3)),
            ),
        )
        self.assertEqual(
            inter_birth_directed_response(state).value,
            (
                (Fraction(2, 1), Fraction(-2, 1)),
                (Fraction(-3, 2), Fraction(3, 2)),
            ),
        )

    def test_every_small_prefix_is_in_exact_domain_and_prebirth_ordered(self) -> None:
        checked = 0
        for b, L in ((2, 2), (2, 3), (3, 2), (4, 1), (2, 4), (3, 3)):
            grammar = build_finite_b_ary_provenance_grammar(
                ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
            )
            schedule = build_canonical_birth_schedule(grammar)
            for n in range(1, len(schedule.slots)):
                with self.subTest(b=b, L=L, n=n):
                    state = _state(b, L, n, extra=(n >= 2))
                    slot = next_open_provenance_slot(state)
                    realization = state_directed_schur_realization(state, slot)
                    self.assertEqual(realization.carrier_order, realization.cut.boundary + realization.cut.interior)
                    self.assertEqual(set(realization.carrier_order), set(state.nodes))
                    self.assertNotIn(slot.child, realization.carrier_order)
                    self.assertTrue(birth_cut_interior_is_admissible(state, realization.blocks, slot))
                    result = inter_birth_directed_response(state, slot)
                    self.assertEqual(result.boundary, realization.cut.boundary)
                    self.assertNotIn(slot.child, result.boundary)
                    self.assertTrue(all(sum(row, Fraction(0, 1)) == 0 for row in result.value))
                    checked += 1
        self.assertEqual(checked, 99)

    def test_response_is_directed_and_scales_with_all_conductances(self) -> None:
        base = inter_birth_directed_response(_state(3, 2, 4, Fraction(1, 1), extra=True))
        scaled = inter_birth_directed_response(_state(3, 2, 4, Fraction(7, 5), extra=True))
        self.assertEqual(base.boundary, scaled.boundary)
        expected = tuple(tuple(Fraction(7, 5) * value for value in row) for row in base.value)
        self.assertEqual(scaled.value, expected)
        self.assertNotEqual(base.value, tuple(zip(*base.value)))

    def test_non_c004_slot_is_rejected_before_matrix_assembly(self) -> None:
        state = _state(2, 3, 3)
        later = state.schedule.slots[state.n + 1]
        with self.assertRaises(ValueError):
            state_directed_schur_realization(state, later)
        with self.assertRaises(ValueError):
            inter_birth_directed_response(state, later)


if __name__ == "__main__":
    unittest.main()
