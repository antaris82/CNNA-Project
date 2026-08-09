"""Paper 1.2.5 / T001 — seed-neutrality theorem for the first birth.

Python supplies the executable side of the theorem: the generated C013 state
is obtained through the same constructor for any admissible GenesisSeed.  Lean
owns the formal equality proof.
"""
from __future__ import annotations

from .s01_c004a__first_provenance_slot_s1 import FirstProvenanceSlot
from .s02_a001__genesis_seed_star import GenesisSeed
from .s03_n001__initial_conductance_normalization_c_star_1 import InitialConductanceNormalization
from .s04_c013__first_non_root_provenance_birth_v1 import FirstNonRootBirth, build_first_non_root_birth


def first_weighted_state_from_seed(
    slot: FirstProvenanceSlot,
    seed: GenesisSeed,
    normalization: InitialConductanceNormalization,
) -> FirstNonRootBirth:
    """Return the C013 first weighted state generated from the explicit seed."""
    return build_first_non_root_birth(slot, seed, normalization)


__all__ = ["first_weighted_state_from_seed"]
