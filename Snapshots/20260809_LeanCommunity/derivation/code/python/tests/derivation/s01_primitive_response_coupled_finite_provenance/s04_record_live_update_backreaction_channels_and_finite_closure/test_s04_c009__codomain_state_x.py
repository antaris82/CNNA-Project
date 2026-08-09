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
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s04_c009__codomain_state_x import (
    assemble_codomain_state_data,
    live_channel_represents_state,
    realize_response_capable_candidate,
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
        value = Fraction(idx + 1, idx)
        edges.extend((
            DirectedConductance(parent, child, value),
            DirectedConductance(child, parent, value),
        ))
    return ResponseCapableState(schedule, born, tuple(edges))


def _channels(state: ResponseCapableState) -> RecordLiveChannels:
    exact = tuple(
        DirectedRelationUpdate(edge.source, edge.target, edge.value)
        for edge in state.conductances
    )
    return RecordLiveChannels(record=exact, live=exact)


def test_c009_assembles_exact_c004_c016_c017_components() -> None:
    state = _state(2, 2, 1)
    channels = _channels(state)
    instruction = direct_response_lift(next_open_provenance_slot(state), Fraction(3, 2))
    output = assemble_codomain_state_data(state, channels, instruction)

    assert output.schedule is state.schedule
    assert output.born_nonroot == state.born_nonroot + (instruction.slot.child,)
    assert output.record[: len(channels.record)] == channels.record
    assert output.record[len(channels.record) :] == instruction.parent_child_birth_updates
    assert output.live[: len(channels.live)] == channels.live
    assert output.live[len(channels.live) :] == instruction.all_relation_updates


def test_c009_rejects_incoherent_live_channel() -> None:
    state = _state(2, 2, 1)
    channels = RecordLiveChannels(record=(), live=())
    instruction = direct_response_lift(next_open_provenance_slot(state), Fraction(1, 1))
    assert not live_channel_represents_state(state, channels)
    with pytest.raises(ValueError):
        assemble_codomain_state_data(state, channels, instruction)


def test_c009_python_realization_is_only_finite_t002_countercheck() -> None:
    checked = 0
    for b, L in ((2, 2), (2, 3), (3, 2)):
        grammar = build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
        )
        schedule = build_canonical_birth_schedule(grammar)
        state = _state(b, L, 1)
        channels = _channels(state)
        while state.n < len(schedule.addresses):
            instruction = direct_response_lift(
                next_open_provenance_slot(state),
                Fraction(state.n + 2, state.n + 1),
            )
            raw = assemble_codomain_state_data(state, channels, instruction)
            next_state = realize_response_capable_candidate(raw)
            assert next_state.n == state.n + 1
            assert next_state.born_nonroot[:-1] == state.born_nonroot
            assert live_channel_represents_state(
                next_state, RecordLiveChannels(raw.record, raw.live)
            )
            state = next_state
            channels = RecordLiveChannels(raw.record, raw.live)
            checked += 1
    assert checked > 20
