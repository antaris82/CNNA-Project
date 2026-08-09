"""Focused tests for Paper 1.3.10 / M004."""
from __future__ import annotations

import inspect
import unittest
from fractions import Fraction
from unittest.mock import patch

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
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState, response_capable_state_from_bootstrap
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s06_c007__inter_birth_directed_response_rn_snplus1 import inter_birth_directed_response
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s07_o001__ist_response_independent_directed_bias_obstruction import AdmittedGrowthLawInputs
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s09_m003__canonical_response_steering_functional_sigma_b_rn_s import (
    CanonicalResponseSteering,
    canonical_response_steering_functional,
)
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import (
    BirthLawDomainError,
    DirectedRelationUpdate,
    canonical_bias_free_birth_law_inputs,
    direct_response_lift,
    response_coupled_birth_law,
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


def _instruction(state: ResponseCapableState):
    response = inter_birth_directed_response(state)
    steering = canonical_response_steering_functional(response)
    inputs = canonical_bias_free_birth_law_inputs(state, response, steering)
    return response, steering, inputs, response_coupled_birth_law(inputs)


class TestResponseCoupledBirthLaw(unittest.TestCase):
    def test_bootstrap_recurrent_birth_is_unit_direct_lift(self) -> None:
        response, steering, inputs, result = _instruction(_bootstrap_state())
        self.assertIsInstance(inputs, AdmittedGrowthLawInputs)
        self.assertEqual(response.slot.parent, ())
        self.assertEqual(response.slot.child, (1,))
        self.assertEqual(steering.value, Fraction(1, 1))
        self.assertEqual(result.birth_lapse, Fraction(1, 1))
        self.assertEqual(result.ancestor_backreaction_updates, ())
        self.assertEqual(
            result.parent_child_birth_updates,
            (
                DirectedRelationUpdate((), (1,), Fraction(1, 1)),
                DirectedRelationUpdate((1,), (), Fraction(1, 1)),
            ),
        )
        self.assertEqual(
            result.sibling_backreaction_updates,
            (
                DirectedRelationUpdate((0,), (1,), Fraction(1, 1)),
                DirectedRelationUpdate((1,), (0,), Fraction(1, 1)),
            ),
        )

    def test_nonroot_birth_uses_strict_ancestor_support_without_parent_duplicate(self) -> None:
        response, steering, _inputs, result = _instruction(_state(2, 2, 2))
        self.assertEqual(response.slot.parent, (0,))
        self.assertEqual(response.slot.child, (0, 0))
        self.assertEqual(steering.value, Fraction(3, 2))
        self.assertEqual(
            result.ancestor_backreaction_updates,
            (DirectedRelationUpdate((0, 0), (), Fraction(3, 2)),),
        )
        self.assertEqual(result.sibling_backreaction_updates, ())
        pairs = tuple((update.source, update.target) for update in result.all_relation_updates)
        self.assertEqual(len(pairs), len(set(pairs)))

    def test_older_sibling_support_has_no_rank_distance_weight(self) -> None:
        _response, steering, _inputs, result = _instruction(_state(3, 2, 2))
        self.assertEqual(result.slot.parent, ())
        self.assertEqual(result.slot.rank, 2)
        self.assertEqual(
            tuple((u.source, u.target) for u in result.sibling_backreaction_updates),
            (((0,), (2,)), ((2,), (0,)), ((1,), (2,)), ((2,), (1,))),
        )
        self.assertTrue(
            all(update.value == steering.value for update in result.all_relation_updates)
        )

    def test_every_small_recurrent_prefix_is_positive_and_directly_response_derived(self) -> None:
        checked = 0
        for b, L in ((2, 2), (2, 3), (3, 2), (4, 1), (2, 4), (3, 3)):
            grammar = build_finite_b_ary_provenance_grammar(
                ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
            )
            schedule = build_canonical_birth_schedule(grammar)
            for n in range(1, len(schedule.slots)):
                with self.subTest(b=b, L=L, n=n):
                    _response, steering, _inputs, result = _instruction(_state(b, L, n))
                    self.assertGreater(steering.value, 0)
                    self.assertEqual(result.birth_lapse, steering.value)
                    self.assertTrue(
                        all(update.value == steering.value for update in result.all_relation_updates)
                    )
                    checked += 1
        self.assertEqual(checked, 99)

    def test_common_conductance_rescaling_scales_every_m004_value(self) -> None:
        _r1, s1, _i1, base = _instruction(_state(3, 2, 4, Fraction(1, 1)))
        _r2, s2, _i2, scaled = _instruction(_state(3, 2, 4, Fraction(7, 5)))
        self.assertEqual(s2.value, Fraction(7, 5) * s1.value)
        self.assertEqual(scaled.birth_lapse, Fraction(7, 5) * base.birth_lapse)
        self.assertEqual(len(base.all_relation_updates), len(scaled.all_relation_updates))
        for left, right in zip(base.all_relation_updates, scaled.all_relation_updates, strict=True):
            self.assertEqual((left.source, left.target), (right.source, right.target))
            self.assertEqual(right.value, Fraction(7, 5) * left.value)

    def test_zero_is_algebraic_boundary_not_active_birth_input(self) -> None:
        state = _bootstrap_state()
        response = inter_birth_directed_response(state)
        slot = response.slot
        zero = direct_response_lift(slot, Fraction(0, 1))
        self.assertEqual(zero.steering_value, Fraction(0, 1))
        self.assertEqual(zero.birth_lapse, Fraction(0, 1))
        self.assertTrue(all(update.value == 0 for update in zero.all_relation_updates))

        parent_index = response.boundary.index(response.slot.parent)
        synthetic_zero = CanonicalResponseSteering(
            birth_count=response.birth_count,
            slot_parent=response.slot.parent,
            matching_boundary_indices=(parent_index,),
            parent_self_response=Fraction(0, 1),
            normalized_response=Fraction(0, 1),
            value=Fraction(0, 1),
        )
        with patch(
            "cnna.derivation.s01_primitive_response_coupled_finite_provenance."
            "s03_recurrent_pre_birth_measurement_and_steering."
            "s10_m004__response_coupled_birth_law_birthlaw_b."
            "canonical_response_steering_functional",
            return_value=synthetic_zero,
        ):
            with self.assertRaisesRegex(BirthLawDomainError, "Sigma_b > 0"):
                canonical_bias_free_birth_law_inputs(state, response, synthetic_zero)
        with self.assertRaises(BirthLawDomainError):
            direct_response_lift(slot, Fraction(-1, 1))

    def test_noncanonical_inputs_and_extra_controls_are_rejected(self) -> None:
        state = _state(2, 2, 2)
        response = inter_birth_directed_response(state)
        steering = canonical_response_steering_functional(response)
        wrong_state = _state(2, 2, 1)
        with self.assertRaises(BirthLawDomainError):
            canonical_bias_free_birth_law_inputs(wrong_state, response, steering)

        admitted = canonical_bias_free_birth_law_inputs(state, response, steering)
        tampered = AdmittedGrowthLawInputs(
            state=admitted.state,
            slot=admitted.slot,
            response=admitted.response,
            steering=canonical_response_steering_functional(
                inter_birth_directed_response(_state(2, 2, 1))
            ),
        )
        with self.assertRaises(BirthLawDomainError):
            response_coupled_birth_law(tampered)

        signature = inspect.signature(response_coupled_birth_law)
        self.assertEqual(tuple(signature.parameters), ("inputs",))
        lift_signature = inspect.signature(direct_response_lift)
        self.assertEqual(tuple(lift_signature.parameters), ("slot", "steering_value"))
        forbidden = {
            "rank", "rank_distance", "depth", "bias", "forward", "backward",
            "mode", "scale", "slope", "baseline", "coefficient", "g",
        }
        self.assertTrue(forbidden.isdisjoint(signature.parameters))
        self.assertTrue(forbidden.isdisjoint(lift_signature.parameters))


if __name__ == "__main__":
    unittest.main()
