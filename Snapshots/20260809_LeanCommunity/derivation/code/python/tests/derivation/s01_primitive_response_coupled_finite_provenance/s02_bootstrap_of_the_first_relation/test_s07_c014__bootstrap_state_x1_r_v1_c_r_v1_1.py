"""Focused test for Paper 1.2.7 / C014."""
from __future__ import annotations

import dataclasses
import unittest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s01_c004a__first_provenance_slot_s1 import build_canonical_first_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s02_a001__genesis_seed_star import GENESIS_SEED
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import INITIAL_CONDUCTANCE_NORMALIZATION
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s04_c013__first_non_root_provenance_birth_v1 import build_first_non_root_birth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import BootstrapState, build_bootstrap_state


class TestBootstrapState(unittest.TestCase):
    def test_x1_is_exactly_the_first_weighted_relation_without_extra_payload(self) -> None:
        grammar = build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(1)
        )
        slot = build_canonical_first_provenance_slot(grammar)
        birth = build_first_non_root_birth(slot, GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
        state = build_bootstrap_state(birth)
        self.assertEqual(state.root, ())
        self.assertEqual(state.newborn, (0,))
        self.assertEqual(state.directed_relations, (((), (0,)), ((0,), ())))
        self.assertEqual(state.directed_conductances, (1, 1))
        self.assertEqual(tuple(f.name for f in dataclasses.fields(BootstrapState)), ("birth",))


if __name__ == "__main__":
    unittest.main()
