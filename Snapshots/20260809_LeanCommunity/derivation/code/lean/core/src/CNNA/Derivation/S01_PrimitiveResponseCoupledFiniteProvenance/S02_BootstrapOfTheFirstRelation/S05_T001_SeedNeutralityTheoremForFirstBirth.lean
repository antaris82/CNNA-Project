import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S04_C013_FirstNonRootProvenanceBirthV1

/-!
Paper 1.2.5 / T001 — seed-neutrality theorem for the first birth.

C013 consumes the explicit singleton bootstrap seed but does not retain it in
the generated first weighted provenance state.  T001 states the resulting
seed-independence as equality of the generated states and records the inherited
unit conductance of the first relation.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

/-- The C013 first weighted state, written as a seed-indexed construction for T001. -/
def firstWeightedStateFromSeed
    (slot : FirstProvenanceSlot)
    (seed : GenesisSeed)
    (normalization : InitialConductanceNormalization)
    (h : FirstProvenanceSlot.WithinCutoff slot) : FirstNonRootBirth :=
  FirstNonRootBirth.build slot seed normalization h

/--
Seed-neutrality of the exceptional first birth: any two admissible bootstrap
seed values generate exactly the same first weighted provenance state, and its
two directed conductances are the fixed N001 unit pair.
-/
theorem seedNeutralityFirstBirth
    (slot : FirstProvenanceSlot)
    (eta etaPrime : GenesisSeed)
    (normalization : InitialConductanceNormalization)
    (h : FirstProvenanceSlot.WithinCutoff slot) :
    firstWeightedStateFromSeed slot eta normalization h =
      firstWeightedStateFromSeed slot etaPrime normalization h
    ∧ FirstNonRootBirth.directedConductances
        (firstWeightedStateFromSeed slot eta normalization h) = (1, 1) := by
  constructor
  · rfl
  · exact FirstNonRootBirth.directedConductances_eq_unit_pair
      (firstWeightedStateFromSeed slot eta normalization h)

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
