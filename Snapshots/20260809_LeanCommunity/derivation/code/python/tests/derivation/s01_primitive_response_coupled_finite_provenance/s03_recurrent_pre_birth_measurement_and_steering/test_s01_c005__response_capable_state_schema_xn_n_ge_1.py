"""Focused tests for Paper 1.3.1 / C005."""
from __future__ import annotations

import unittest
from fractions import Fraction

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s01_c004a__first_provenance_slot_s1 import build_canonical_first_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s02_a001__genesis_seed_star import GENESIS_SEED
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import INITIAL_CONDUCTANCE_NORMALIZATION
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s04_c013__first_non_root_provenance_birth_v1 import build_first_non_root_birth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import build_bootstrap_state
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState, response_capable_state_from_bootstrap


def _x1():
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(2)
    )
    slot = build_canonical_first_provenance_slot(grammar)
    birth = build_first_non_root_birth(slot, GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
    return build_bootstrap_state(birth)


class TestResponseCapableStateSchema(unittest.TestCase):
    def test_c014_is_exact_c005_base_case(self) -> None:
        state = response_capable_state_from_bootstrap(_x1())
        self.assertEqual(state.n, 1)
        self.assertEqual(state.nodes, ((), (0,)))
        self.assertEqual(state.born_nonroot, ((0,),))
        self.assertEqual(state.conductance((), (0,)), Fraction(1, 1))
        self.assertEqual(state.conductance((0,), ()), Fraction(1, 1))

    def test_generic_recurrent_prefix_and_schema_guards(self) -> None:
        base = response_capable_state_from_bootstrap(_x1())
        edges = (
            DirectedConductance((), (0,), Fraction(1, 1)),
            DirectedConductance((0,), (), Fraction(1, 1)),
            DirectedConductance((), (1,), Fraction(3, 2)),
            DirectedConductance((1,), (), Fraction(4, 3)),
        )
        state2 = ResponseCapableState(base.schedule, ((0,), (1,)), edges)
        self.assertEqual(state2.n, 2)
        self.assertEqual(state2.nodes, ((), (0,), (1,)))

        # Skipping the second C018 birth is not an admissible X_n.
        with self.assertRaises(ValueError):
            ResponseCapableState(base.schedule, ((0,), (0, 0)), edges)

        # A born child must retain both directed parent-child conductances.
        with self.assertRaises(ValueError):
            ResponseCapableState(
                base.schedule,
                base.born_nonroot,
                (DirectedConductance((), (0,), Fraction(1, 1)),),
            )


if __name__ == "__main__":
    unittest.main()
