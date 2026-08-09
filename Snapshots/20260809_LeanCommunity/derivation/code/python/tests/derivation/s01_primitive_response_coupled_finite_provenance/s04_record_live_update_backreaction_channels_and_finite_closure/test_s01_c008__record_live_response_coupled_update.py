from __future__ import annotations

import inspect
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
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s02_bootstrap_of_the_first_relation.s07_c014__bootstrap_state_x1_r_v1_c_r_v1_1 import build_bootstrap_state
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s01_c005__response_capable_state_schema_xn_n_ge_1 import DirectedConductance, ResponseCapableState
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s06_c007__inter_birth_directed_response_rn_snplus1 import inter_birth_directed_response
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s09_m003__canonical_response_steering_functional_sigma_b_rn_s import canonical_response_steering_functional
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s10_m004__response_coupled_birth_law_birthlaw_b import (
    DirectedRelationUpdate,
    canonical_bias_free_birth_law_inputs,
    response_coupled_birth_law,
)
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s04_record_live_update_backreaction_channels_and_finite_closure.s01_c008__record_live_response_coupled_update import (
    RecordLiveChannels,
    apply_response_coupled_update,
    bootstrap_record_live_channels,
    live_instruction_updates,
    record_instruction_updates,
)


def _bootstrap():
    grammar = build_finite_b_ary_provenance_grammar(
        ROOTED_CARRIER, BranchingParameter(2), FiniteApproximantDepth(2)
    )
    slot = build_canonical_first_provenance_slot(grammar)
    birth = build_first_non_root_birth(slot, GENESIS_SEED, INITIAL_CONDUCTANCE_NORMALIZATION)
    return build_bootstrap_state(birth)


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


def _instruction(state: ResponseCapableState):
    response = inter_birth_directed_response(state)
    steering = canonical_response_steering_functional(response)
    inputs = canonical_bias_free_birth_law_inputs(state, response, steering)
    return response_coupled_birth_law(inputs)


def test_bootstrap_initializes_record_and_live_from_same_derived_x1_pair() -> None:
    channels = bootstrap_record_live_channels(_bootstrap())
    expected = (
        DirectedRelationUpdate((), (0,), Fraction(1, 1)),
        DirectedRelationUpdate((0,), (), Fraction(1, 1)),
    )
    assert channels.record == expected
    assert channels.live == expected


def test_record_gets_only_new_birth_pair_while_live_gets_backreaction() -> None:
    instruction = _instruction(_state(2, 2, 1))
    channels = bootstrap_record_live_channels(_bootstrap())
    updated = apply_response_coupled_update(channels, instruction)

    assert updated.record[: len(channels.record)] == channels.record
    assert updated.live[: len(channels.live)] == channels.live
    assert updated.record[len(channels.record) :] == instruction.parent_child_birth_updates
    assert updated.live[len(channels.live) :] == instruction.all_relation_updates
    assert instruction.sibling_backreaction_updates
    assert not instruction.ancestor_backreaction_updates


def test_strict_ancestor_backreaction_is_live_only() -> None:
    instruction = _instruction(_state(2, 2, 2))
    channels = RecordLiveChannels((), ())
    updated = apply_response_coupled_update(channels, instruction)

    assert instruction.ancestor_backreaction_updates == (
        DirectedRelationUpdate((0, 0), (), Fraction(3, 2)),
    )
    assert updated.record == instruction.parent_child_birth_updates
    assert updated.live == instruction.all_relation_updates
    ancestor_pair = ((0, 0), ())
    assert ancestor_pair not in tuple((u.source, u.target) for u in updated.record)
    assert ancestor_pair in tuple((u.source, u.target) for u in updated.live)


def test_old_channel_entries_are_preserved_exactly_as_prefixes() -> None:
    old_record = (DirectedRelationUpdate((), (0,), Fraction(5, 7)),)
    old_live = (DirectedRelationUpdate((0,), (), Fraction(11, 13)),)
    channels = RecordLiveChannels(old_record, old_live)
    instruction = _instruction(_state(3, 2, 2))
    updated = apply_response_coupled_update(channels, instruction)

    assert updated.record[:1] is not old_record  # tuple slicing is a value comparison, not mutation
    assert updated.record[:1] == old_record
    assert updated.live[:1] == old_live
    assert channels.record == old_record
    assert channels.live == old_live


def test_c008_has_no_legacy_free_update_controls() -> None:
    signature = inspect.signature(apply_response_coupled_update)
    assert tuple(signature.parameters) == ("channels", "instruction")
    forbidden = {
        "rank", "rank_distance", "depth", "bias", "forward", "backward",
        "mode", "scale", "slope", "baseline", "coefficient", "g", "node_load",
        "ancestor_coefficient", "sibling_coefficient",
    }
    assert forbidden.isdisjoint(signature.parameters)


def test_small_finite_sweep_matches_m004_channel_partition_exactly() -> None:
    checked = 0
    for b, L in ((2, 2), (2, 3), (3, 2), (4, 1), (2, 4), (3, 3)):
        grammar = build_finite_b_ary_provenance_grammar(
            ROOTED_CARRIER, BranchingParameter(b), FiniteApproximantDepth(L)
        )
        schedule = build_canonical_birth_schedule(grammar)
        for n in range(1, len(schedule.slots)):
            instruction = _instruction(_state(b, L, n))
            assert record_instruction_updates(instruction) == instruction.parent_child_birth_updates
            assert live_instruction_updates(instruction) == instruction.all_relation_updates
            updated = apply_response_coupled_update(RecordLiveChannels((), ()), instruction)
            assert updated.record == instruction.parent_child_birth_updates
            assert updated.live == instruction.all_relation_updates
            checked += 1
    assert checked == 99
