"""Focused tests for Paper 1.3.7 / O001."""
from __future__ import annotations

import unittest
from cnna.derivation.s01_primitive_response_coupled_finite_provenance.s03_recurrent_pre_birth_measurement_and_steering.s07_o001__ist_response_independent_directed_bias_obstruction import (
    CHANNEL_ORDER,
    LEGACY_RANK_FORWARD_BACKWARD_BIAS,
    LEGACY_RESPONSE_INDEPENDENT_CHANNELS,
    NO_INDEPENDENT_DIRECTED_BIAS,
    CandidateGrowthLawInputs,
    IndependentDirectedBiasPresence,
    ResponseIndependentBiasError,
    admit_growth_law_inputs,
    audit_legacy_response_independent_bias,
)


def _presence_only(channel: str) -> IndependentDirectedBiasPresence:
    values = {name: name == channel for name in CHANNEL_ORDER}
    return IndependentDirectedBiasPresence(**values)


class TestIstResponseIndependentDirectedBiasObstruction(unittest.TestCase):
    def test_each_independent_channel_is_explicitly_rejected(self) -> None:
        for channel in CHANNEL_ORDER:
            with self.subTest(channel=channel):
                candidate = CandidateGrowthLawInputs(
                    state="X_n",
                    slot="s_n+1",
                    response="R_n",
                    steering="Sigma_b",
                    independent_bias=_presence_only(channel),
                )
                with self.assertRaisesRegex(ResponseIndependentBiasError, channel):
                    admit_growth_law_inputs(candidate)

    def test_bias_free_admission_preserves_exactly_the_four_m004_inputs(self) -> None:
        state = object()
        slot = object()
        response = object()
        steering = object()
        candidate = CandidateGrowthLawInputs(
            state=state,
            slot=slot,
            response=response,
            steering=steering,
            independent_bias=NO_INDEPENDENT_DIRECTED_BIAS,
        )
        admitted = admit_growth_law_inputs(candidate)
        self.assertIs(admitted.state, state)
        self.assertIs(admitted.slot, slot)
        self.assertIs(admitted.response, response)
        self.assertIs(admitted.steering, steering)
        self.assertFalse(hasattr(admitted, "independent_bias"))

    def test_historical_and_full_legacy_witnesses_are_rejected(self) -> None:
        self.assertEqual(
            LEGACY_RANK_FORWARD_BACKWARD_BIAS.active_channels,
            ("rank", "forward", "backward"),
        )
        self.assertEqual(
            LEGACY_RESPONSE_INDEPENDENT_CHANNELS.active_channels,
            CHANNEL_ORDER,
        )
        for witness in (
            LEGACY_RANK_FORWARD_BACKWARD_BIAS,
            LEGACY_RESPONSE_INDEPENDENT_CHANNELS,
        ):
            with self.subTest(witness=witness.active_channels):
                candidate = CandidateGrowthLawInputs(
                    state=1,
                    slot=2,
                    response=3,
                    steering=4,
                    independent_bias=witness,
                )
                with self.assertRaises(ResponseIndependentBiasError):
                    admit_growth_law_inputs(candidate)

    def test_ast_audit_ignores_comments_and_detects_executable_use_only(self) -> None:
        harmless = '''
class Rule:
    def _mode_scale(self, x):
        # log1p mode
        return x
    def _make_growth_step(self, slot, linearization_index):
        """birth_g additive_unit_baseline"""
        return slot
    def _base_birth_edge_weights(self, step):
        # forward_rank_bias backward_base backward_rank_bias
        return step
    def _add_slot_sibling_relations(self, parent, child, siblings, w0):
        """sibling_forward_asym sibling_backward_asym"""
        return w0
'''
        audit = audit_legacy_response_independent_bias(harmless)
        self.assertEqual(audit.findings, ())
        self.assertFalse(audit.obstruction_present)

        executable = '''
import math
class RC:
    forward_rank_bias = 1
    child_env_load = 1
class Rule:
    def _mode_scale(self, x):
        return math.log1p(x)
    def _make_growth_step(self, slot, linearization_index):
        birth_g = 1.0 + self._mode_scale(slot.env_load)
        return birth_g
    def _base_birth_edge_weights(self, step):
        return self.rc.forward_rank_bias * step.slot.sibling_rank
    def _apply_growth_step(self, step):
        return self.rc.child_env_load * step.env_load
    def _add_slot_sibling_relations(self, parent, child, siblings, w0):
        return w0
'''
        audit = audit_legacy_response_independent_bias(executable)
        self.assertEqual(
            audit.active_channels,
            (
                "rank",
                "forward",
                "node_load_scalar",
                "nonlinear_mode",
                "additive_baseline",
            ),
        )
        self.assertFalse(audit.obstruction_present)


if __name__ == "__main__":
    unittest.main()
