from __future__ import annotations

import pytest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s01_c004a__first_provenance_slot_s1 import build_first_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s02_a001__genesis_seed_star import GENESIS_SEED
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s03_n001__initial_conductance_normalization_c_star_1 import INITIAL_CONDUCTANCE_NORMALIZATION
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s04_c013__first_non_root_provenance_birth_v1 import build_first_non_root_birth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import build_bootstrap_state
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import response_capable_state_from_bootstrap
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s01_c008__record_live_response_coupled_update import RecordLiveChannels, bootstrap_record_live_channels
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s04_c009__codomain_state_x import live_channel_represents_state
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s05_t002__recurrent_state_closure_theorem import recurrent_state_successor


def _bootstrap(b: int, L: int):
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
    )
    schedule = build_canonical_birth_schedule(grammar)
    slot = build_first_provenance_slot(grammar, schedule)
    birth = build_first_non_root_birth(slot, GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
    bootstrap = build_bootstrap_state(birth)
    return response_capable_state_from_bootstrap(bootstrap), bootstrap_record_live_channels(bootstrap)


def test_t002_one_step_reenters_c005_and_preserves_channel_handoff() -> None:
    state, channels = _bootstrap(2, 2)
    closed = recurrent_state_successor(state, channels)

    assert closed.successor.n == 2
    assert closed.successor.born_nonroot[:-1] == state.born_nonroot
    assert closed.raw_codomain.born_nonroot == closed.successor.born_nonroot
    assert closed.raw_codomain.live == closed.channels.live
    assert live_channel_represents_state(closed.successor, closed.channels)


def test_t002_iterates_while_the_finite_c004_schedule_has_an_open_slot() -> None:
    state, channels = _bootstrap(2, 2)
    total = len(state.schedule.addresses)
    steps = 0
    while state.n < total:
        closed = recurrent_state_successor(state, channels)
        state, channels = closed.successor, closed.channels
        steps += 1
    assert state.n == total
    assert steps == total - 1


def test_t002_rejects_incoherent_pre_step_live_channel() -> None:
    state, channels = _bootstrap(2, 2)
    bad = RecordLiveChannels(record=channels.record, live=())
    with pytest.raises(ValueError):
        recurrent_state_successor(state, bad)
