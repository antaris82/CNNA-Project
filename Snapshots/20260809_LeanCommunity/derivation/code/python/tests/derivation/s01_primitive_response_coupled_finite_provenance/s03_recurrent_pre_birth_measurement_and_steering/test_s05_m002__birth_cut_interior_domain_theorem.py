"""Focused tests for Paper 1.3.5 / M002."""
from __future__ import annotations

import unittest
from fractions import Fraction

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s03_c006__birth_local_schur_dtn_primitive import OrderedSchurBlocks, interior_is_admissible
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s04_m001__canonical_birth_local_measurement_cut_cn_snplus1 import canonical_birth_local_measurement_cut
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s05_m002__birth_cut_interior_domain_theorem import (
    birth_cut_interior_is_admissible,
    domain_contrast_witness,
    validate_birth_cut_block_dimensions,
)


def _state(b: int, L: int, n: int) -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
    )
    schedule = build_canonical_birth_schedule(grammar)
    born = schedule.addresses[:n]
    edges: list[DirectedConductance] = []
    for idx, child in enumerate(born, start=1):
        parent = grammar.parent(child)
        edges.append(DirectedConductance(parent, child, Fraction(idx + 1, idx)))
        edges.append(DirectedConductance(child, parent, Fraction(idx + 2, idx + 1)))
    return ResponseCapableState(schedule, born, tuple(edges))


def _zero(rows: int, cols: int):
    return tuple(tuple(Fraction(0, 1) for _ in range(cols)) for _ in range(rows))


class TestBirthCutInteriorDomainTheorem(unittest.TestCase):
    def test_exact_domain_is_c006_admissibility_with_m001_dimensions(self) -> None:
        state = _state(2, 2, 2)
        cut = canonical_birth_local_measurement_cut(state)
        self.assertEqual(len(cut.interior), 1)
        b, i = len(cut.boundary), len(cut.interior)
        good = OrderedSchurBlocks(_zero(b, b), _zero(b, i), _zero(i, b), ((Fraction(3, 2),),))
        bad = OrderedSchurBlocks(_zero(b, b), _zero(b, i), _zero(i, b), ((Fraction(0, 1),),))
        self.assertEqual(birth_cut_interior_is_admissible(state, good), interior_is_admissible(good))
        self.assertEqual(birth_cut_interior_is_admissible(state, bad), interior_is_admissible(bad))
        self.assertTrue(birth_cut_interior_is_admissible(state, good))
        self.assertFalse(birth_cut_interior_is_admissible(state, bad))

    def test_same_nonempty_cut_has_admissible_and_singular_assignments(self) -> None:
        for b, L, n in ((2, 2, 2), (2, 3, 3), (3, 2, 3), (3, 3, 7)):
            with self.subTest(b=b, L=L, n=n):
                state = _state(b, L, n)
                witness = domain_contrast_witness(state)
                self.assertGreater(len(witness.cut.interior), 0)
                self.assertTrue(interior_is_admissible(witness.admissible_blocks))
                self.assertFalse(interior_is_admissible(witness.inadmissible_blocks))
                self.assertEqual(witness.admissible_blocks.boundary_size, len(witness.cut.boundary))
                self.assertEqual(witness.inadmissible_blocks.interior_size, len(witness.cut.interior))

    def test_zero_interior_is_unconditionally_in_c006_domain(self) -> None:
        state = _state(2, 2, 1)
        cut = canonical_birth_local_measurement_cut(state)
        self.assertEqual(cut.interior, ())
        b = len(cut.boundary)
        blocks = OrderedSchurBlocks(
            tuple(tuple(Fraction(7 if r == c else -2, 3) for c in range(b)) for r in range(b)),
            _zero(b, 0),
            (),
            (),
        )
        self.assertTrue(birth_cut_interior_is_admissible(state, blocks))
        with self.assertRaises(ValueError):
            domain_contrast_witness(state)

    def test_dimension_mismatch_is_rejected_before_domain_test(self) -> None:
        state = _state(2, 2, 2)
        cut = canonical_birth_local_measurement_cut(state)
        wrong = OrderedSchurBlocks(
            ((Fraction(1, 1),),),
            ((Fraction(0, 1),),),
            ((Fraction(0, 1),),),
            ((Fraction(1, 1),),),
        )
        with self.assertRaises(ValueError):
            validate_birth_cut_block_dimensions(cut, wrong)
        with self.assertRaises(ValueError):
            birth_cut_interior_is_admissible(state, wrong)


if __name__ == "__main__":
    unittest.main()
