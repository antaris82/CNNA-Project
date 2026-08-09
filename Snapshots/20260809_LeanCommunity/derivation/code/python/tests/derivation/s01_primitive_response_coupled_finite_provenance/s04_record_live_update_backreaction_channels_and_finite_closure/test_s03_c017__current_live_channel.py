from __future__ import annotations

from fractions import Fraction

import pytest

from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s01_i001__branching_parameter_b import BranchingParameter
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s02_i002__finite_approximant_depth_l import FiniteApproximantDepth
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s04_c002__root_genesis_r import ROOTED_CARRIER
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s05_c003__finite_b_ary_provenance_grammar import build_finite_b_ary_provenance_grammar
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s01_primitive_inputs_grammar_and_event_order.s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule import build_canonical_birth_schedule
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s02_c004__next_open_provenance_slot_snplus1_n_ge_1 import next_open_provenance_slot
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import DirectedRelationUpdate, direct_response_lift
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s01_c008__record_live_response_coupled_update import RecordLiveChannels
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s03_c017__current_live_channel import current_live_channel, live_channel_after_instruction


def _state(n: int) -> ResponseCapableState:
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(2)
    )
    schedule = build_canonical_birth_schedule(grammar)
    born = schedule.addresses[:n]
    edges = []
    for child in born:
        parent = grammar.parent(child)
        edges.extend((
            DirectedConductance(parent, child, Fraction(1, 1)),
            DirectedConductance(child, parent, Fraction(1, 1)),
        ))
    return ResponseCapableState(schedule, born, tuple(edges))


def test_c017_is_exact_projection_of_existing_live_channel() -> None:
    old = (DirectedRelationUpdate((0,), (), Fraction(11, 13)),)
    channels = RecordLiveChannels(record=(), live=old)
    assert current_live_channel(channels) is old


def test_c017_preserves_old_live_and_appends_complete_m004_delta() -> None:
    state = _state(2)
    instruction = direct_response_lift(next_open_provenance_slot(state), Fraction(3, 2))
    old = (DirectedRelationUpdate((0,), (), Fraction(11, 13)),)
    channels = RecordLiveChannels(record=(), live=old)
    after = live_channel_after_instruction(channels, instruction)

    assert after[: len(old)] == old
    assert after[len(old) :] == instruction.all_relation_updates
    assert instruction.ancestor_backreaction_updates
    assert all(update in after for update in instruction.ancestor_backreaction_updates)


def test_c017_includes_sibling_backreaction_when_m004_emits_it() -> None:
    state = _state(1)
    instruction = direct_response_lift(next_open_provenance_slot(state), Fraction(4, 3))
    channels = RecordLiveChannels(record=(), live=())
    after = live_channel_after_instruction(channels, instruction)

    assert instruction.sibling_backreaction_updates
    assert after == instruction.all_relation_updates
    assert all(update in after for update in instruction.sibling_backreaction_updates)


def test_c017_rejects_non_c008_channel() -> None:
    with pytest.raises(TypeError):
        current_live_channel(())  # type: ignore[arg-type]
