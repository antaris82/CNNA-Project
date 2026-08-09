import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S04_C013_FirstNonRootProvenanceBirthV1
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S05_T001_SeedNeutralityTheoremForFirstBirth
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S06_M005_ConductanceUnitNormalizationIndependence

/-!
Paper 1.2.7 / C014 — bootstrap state X₁.

C014 packages the exceptional C013 birth as the first weighted provenance
state.  T001 certifies that this state is independent of the bootstrap seed;
M005 certifies that N001's value one is only the canonical representative of a
positive rational conductance-unit equivalence class.

The state stores neither a seed nor a unit-choice variable.  No response value
is computed here; the first nontrivial weighted relation is merely now present
for later response constructions.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- First response-capable weighted provenance state. -/
structure BootstrapState where
  birth : FirstNonRootBirth

namespace BootstrapState

/-- Package the completed exceptional first birth as X₁. -/
def build (birth : FirstNonRootBirth) : BootstrapState :=
  ⟨birth⟩

/-- Root endpoint inherited from C013. -/
def rootAddress (X : BootstrapState) : ProvenanceAddress X.birth.slot.grammar.branching :=
  FirstNonRootBirth.rootAddress X.birth

/-- First non-root endpoint inherited from C013. -/
def newbornAddress (X : BootstrapState) : ProvenanceAddress X.birth.slot.grammar.branching :=
  FirstNonRootBirth.newbornAddress X.birth

/-- The first relation retains the symmetric N001 unit conductance pair. -/
theorem directedConductances_eq_unit_pair (X : BootstrapState) :
    FirstNonRootBirth.directedConductances X.birth = (1, 1) :=
  FirstNonRootBirth.directedConductances_eq_unit_pair X.birth

/-- C014 inherits T001 seed-neutrality: changing the bootstrap seed does not change X₁. -/
theorem fromSeed_seedNeutral
    (slot : FirstProvenanceSlot)
    (eta etaPrime : GenesisSeed)
    (normalization : InitialConductanceNormalization)
    (h : FirstProvenanceSlot.WithinCutoff slot) :
    build (firstWeightedStateFromSeed slot eta normalization h) =
      build (firstWeightedStateFromSeed slot etaPrime normalization h) := by
  exact congrArg build (seedNeutralityFirstBirth slot eta etaPrime normalization h).1

/-- Rational lift of the actual C014 directed conductance pair. -/
def directedConductancesRat (X : BootstrapState) : Rat × Rat :=
  (((FirstNonRootBirth.directedConductances X.birth).1 : Rat),
    ((FirstNonRootBirth.directedConductances X.birth).2 : Rat))

/-- The actual C014 pair is exactly the N001 representative in both orientations. -/
theorem directedConductancesRat_eq_n001_pair (X : BootstrapState) :
    directedConductancesRat X =
      (n001ConductanceUnit X.birth.normalization,
        n001ConductanceUnit X.birth.normalization) := by
  unfold directedConductancesRat n001ConductanceUnit
  unfold FirstNonRootBirth.directedConductances
    InitialConductanceNormalization.directedValues
  rfl

/--
C014 applies M005 to its actual stored directed conductances.  A positive
common rescaling changes only their unit representative; it does not construct
a second bootstrap state or add a unit-choice payload to X₁.
-/
theorem conductanceUnit_isRepresentativeOnly
    (X : BootstrapState)
    (scale : Rat)
    (hscale : 0 < scale) :
    SameNormalizedResponse
        (directedConductancesRat X).1
        (n001ConductanceUnit X.birth.normalization)
        (scale * (directedConductancesRat X).1)
        (scale * n001ConductanceUnit X.birth.normalization) ∧
      SameNormalizedResponse
        (directedConductancesRat X).2
        (n001ConductanceUnit X.birth.normalization)
        (scale * (directedConductancesRat X).2)
        (scale * n001ConductanceUnit X.birth.normalization) := by
  constructor
  · exact commonPositiveRescalingPreservesNormalizedResponse
      (directedConductancesRat X).1
      (n001ConductanceUnit X.birth.normalization) scale hscale
  · exact commonPositiveRescalingPreservesNormalizedResponse
      (directedConductancesRat X).2
      (n001ConductanceUnit X.birth.normalization) scale hscale

end BootstrapState

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
