"""Focused tests for Paper 1.2.4 / C013."""
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
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s04_c013__first_non_root_provenance_birth_v1 import FirstNonRootBirth, build_first_non_root_birth


def slot_at_depth(L: int):
    grammar = build_finite_b_ary_provenance_grammar(ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(L))
    return build_canonical_first_provenance_slot(grammar)


class TestFirstNonRootBirth(unittest.TestCase):
    def test_birth_creates_first_root_child_with_unit_directed_weights(self) -> None:
        birth = build_first_non_root_birth(slot_at_depth(1), GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
        self.assertEqual(birth.root, ())
        self.assertEqual(birth.newborn, (0,))
        self.assertEqual(birth.directed_relations, (((), (0,)), ((0,), ())))
        self.assertEqual(birth.directed_conductances, (1, 1))

    def test_birth_requires_first_slot_inside_cutoff_and_retains_no_seed(self) -> None:
        with self.assertRaises(ValueError):
            build_first_non_root_birth(slot_at_depth(0), GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
        self.assertEqual(tuple(f.name for f in dataclasses.fields(FirstNonRootBirth)), ("slot", "normalization"))


if __name__ == "__main__":
    unittest.main()
