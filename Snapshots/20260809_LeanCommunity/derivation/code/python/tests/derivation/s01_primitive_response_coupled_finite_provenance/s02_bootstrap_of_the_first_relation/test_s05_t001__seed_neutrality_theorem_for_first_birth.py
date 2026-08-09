"""Focused executable check for Paper 1.2.5 / T001."""
from __future__ import annotations

import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s01_c004a__first_provenance_slot_s1 import build_canonical_first_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s02_a001__genesis_seed_star import GenesisSeed
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import INITIAL_CONDUCTANCE_NORMALIZATION
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s05_t001__seed_neutrality_theorem_for_first_birth import first_weighted_state_from_seed


class TestSeedNeutralityFirstBirth(unittest.TestCase):
    def test_distinct_seed_instances_generate_identical_first_weighted_state(self) -> None:
        grammar = build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(1)
        )
        slot = build_canonical_first_provenance_slot(grammar)
        eta, eta_prime = GenesisSeed(), GenesisSeed()
        self.assertIsNot(eta, eta_prime)
        left = first_weighted_state_from_seed(slot, eta, INITIAL_CONDUCTANCE_NORMALIZATION)
        right = first_weighted_state_from_seed(slot, eta_prime, INITIAL_CONDUCTANCE_NORMALIZATION)
        self.assertEqual(left, right)
        self.assertEqual(left.directed_conductances, (1, 1))


if __name__ == "__main__":
    unittest.main()
