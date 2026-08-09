"""Focused tests for Paper 1.3.9 / M003."""
from __future__ import annotations

import inspect
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
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s06_m005__conductance_unit_normalization_independence import common_positive_rescaling_preserves_normalized_response
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import build_bootstrap_state
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import (
    DirectedConductance,
    ResponseCapableState,
    response_capable_state_from_bootstrap,
)
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s06_c007__inter_birth_directed_response_rn_snplus1 import inter_birth_directed_response
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s09_m003__canonical_response_steering_functional_sigma_b_rn_s import (
    CanonicalResponseSteering,
    canonical_response_steering_functional,
    is_positive_response_steering,
    parent_port_self_response,
)


def _bootstrap_state() -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(2)
    )
    slot = build_canonical_first_provenance_slot(grammar)
    birth = build_first_non_root_birth(slot, GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
    return response_capable_state_from_bootstrap(build_bootstrap_state(birth))


def _state(b: int, L: int, n: int, scale: Fraction = Fraction(1, 1)) -> ResponseCapableState:
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
    return ResponseCapableState(schedule, born, tuple(edges))


class TestCanonicalResponseSteeringFunctional(unittest.TestCase):
    def test_bootstrap_extracts_unit_parent_response(self) -> None:
        response = inter_birth_directed_response(_bootstrap_state())
        result = canonical_response_steering_functional(response)
        self.assertIsInstance(result, CanonicalResponseSteering)
        self.assertEqual(result.slot_parent, ())
        self.assertEqual(result.matching_boundary_indices, (0,))
        self.assertEqual(result.parent_self_response, Fraction(1, 1))
        self.assertEqual(result.normalized_response, Fraction(1, 1))
        self.assertEqual(result.value, Fraction(1, 1))

    def test_nonroot_parent_uses_its_canonical_boundary_diagonal(self) -> None:
        response = inter_birth_directed_response(_state(2, 2, 2))
        self.assertEqual(response.slot.child, (0, 0))
        self.assertEqual(response.slot.parent, (0,))
        self.assertEqual(response.boundary, ((), (0,)))
        matching, raw = parent_port_self_response(response)
        self.assertEqual(matching, (1,))
        self.assertEqual(raw, Fraction(3, 2))
        self.assertEqual(canonical_response_steering_functional(response).value, Fraction(3, 2))

    def test_every_small_recurrent_prefix_uses_parent_exactly_once(self) -> None:
        checked = 0
        for b, L in ((2, 2), (2, 3), (3, 2), (4, 1), (2, 4), (3, 3)):
            grammar = build_finite_b_ary_provenance_grammar(
                ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
            )
            schedule = build_canonical_birth_schedule(grammar)
            for n in range(1, len(schedule.slots)):
                with self.subTest(b=b, L=L, n=n):
                    response = inter_birth_directed_response(_state(b, L, n))
                    result = canonical_response_steering_functional(response)
                    parent = response.slot.parent
                    expected_indices = tuple(
                        index for index, address in enumerate(response.boundary)
                        if address == parent
                    )
                    self.assertEqual(len(expected_indices), 1)
                    self.assertEqual(result.matching_boundary_indices, expected_indices)
                    self.assertEqual(
                        result.value,
                        response.value[expected_indices[0]][expected_indices[0]],
                    )
                    self.assertTrue(result.is_positive)
                    self.assertTrue(is_positive_response_steering(result))
                    checked += 1
        self.assertEqual(checked, 99)

    def test_common_conductance_rescaling_scales_sigma_b_without_hidden_normalization(self) -> None:
        base = canonical_response_steering_functional(
            inter_birth_directed_response(_state(3, 2, 4, Fraction(1, 1)))
        )
        scaled = canonical_response_steering_functional(
            inter_birth_directed_response(_state(3, 2, 4, Fraction(7, 5)))
        )
        self.assertEqual(scaled.value, Fraction(7, 5) * base.value)
        self.assertEqual(base.value, base.parent_self_response)
        self.assertEqual(scaled.value, scaled.parent_self_response)

    def test_m005_common_unit_rescaling_preserves_the_normalized_datum(self) -> None:
        result = canonical_response_steering_functional(
            inter_birth_directed_response(_state(3, 2, 4))
        )
        self.assertTrue(
            common_positive_rescaling_preserves_normalized_response(
                result.parent_self_response,
                Fraction(1, 1),
                Fraction(11, 7),
            )
        )


    def test_positivity_is_an_explicit_domain_check_not_a_constructor_invariant(self) -> None:
        zero = CanonicalResponseSteering(
            birth_count=1,
            slot_parent=(),
            matching_boundary_indices=(0,),
            parent_self_response=Fraction(0, 1),
            normalized_response=Fraction(0, 1),
            value=Fraction(0, 1),
        )
        self.assertFalse(zero.is_positive)
        self.assertFalse(is_positive_response_steering(zero))

    def test_public_function_has_response_only_api_and_no_birth_update_controls(self) -> None:
        signature = inspect.signature(canonical_response_steering_functional)
        self.assertEqual(tuple(signature.parameters), ("response",))
        self.assertEqual(
            signature.parameters["response"].kind,
            inspect.Parameter.POSITIONAL_ONLY,
        )
        forbidden = {"rank", "bias", "forward", "backward", "mode", "scale", "slope", "birth", "state"}
        self.assertTrue(forbidden.isdisjoint(signature.parameters))


if __name__ == "__main__":
    unittest.main()
