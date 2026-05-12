import CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure CanonicalIdealAlgebraizationResearchSlot where
  idealHasCanonicalOctonionicAlgebra : DirectedFamily (Cell := Cell) → Prop
  canonicalTriadicMultiplication : CayleyDicksonSource Cell T → Prop
  dualCompatibleConjugation : CayleyDicksonSource Cell T → Prop
  positiveDefiniteNormSq : CayleyDicksonSource Cell T → Prop
  alternativeLaw : CayleyDicksonSource Cell T → Prop
  divisionFromNormSq : CayleyDicksonSource Cell T → Prop
  externalHurwitzCompatibility : CayleyDicksonSource Cell T → Prop

structure FunctorialApproximantCompatibilityResearchSlot where
  approximantsExposeProjectiveSubregimes : CayleyDicksonSource Cell T → Prop

structure RegimeRecoveryResearchSlot where
  realToIdealLimitRealizesAlgebraLift : CayleyDicksonSource Cell T → Prop

structure S6ResearchSchema where
  canonicalIdealAlgebraization :
    CanonicalIdealAlgebraizationResearchSlot (Cell := Cell) (T := T)
  functorialApproximantCompatibility :
    FunctorialApproximantCompatibilityResearchSlot (Cell := Cell) (T := T)
  regimeRecovery : RegimeRecoveryResearchSlot (Cell := Cell) (T := T)

def S6ResearchSchema.toConjectureLayer
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    S6ConjectureLayer X :=
  s6_conjecture_layer
    schema.canonicalIdealAlgebraization.idealHasCanonicalOctonionicAlgebra
    schema.functorialApproximantCompatibility.approximantsExposeProjectiveSubregimes
    schema.regimeRecovery.realToIdealLimitRealizesAlgebraLift
    X

def S6ResearchSchema.toOpenProofObligations
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    S6OpenProofObligations X :=
  s6_open_proof_obligations
    schema.canonicalIdealAlgebraization.idealHasCanonicalOctonionicAlgebra
    schema.functorialApproximantCompatibility.approximantsExposeProjectiveSubregimes
    schema.regimeRecovery.realToIdealLimitRealizesAlgebraLift
    X

def S6ResearchSchema.toHurwitzUpgradeSchema
    (schema : S6ResearchSchema (Cell := Cell) (T := T)) :
    HurwitzUpgradeSchema (Cell := Cell) (T := T) where
  canonicalIdealAlgebraization :=
    schema.canonicalIdealAlgebraization.idealHasCanonicalOctonionicAlgebra
  approximantProjectionCompatibility :=
    schema.functorialApproximantCompatibility.approximantsExposeProjectiveSubregimes
  regimeRecovery := schema.regimeRecovery.realToIdealLimitRealizesAlgebraLift
  canonicalTriadicMultiplication :=
    schema.canonicalIdealAlgebraization.canonicalTriadicMultiplication
  dualCompatibleConjugation :=
    schema.canonicalIdealAlgebraization.dualCompatibleConjugation
  positiveDefiniteNormSq :=
    schema.canonicalIdealAlgebraization.positiveDefiniteNormSq
  alternativeLaw := schema.canonicalIdealAlgebraization.alternativeLaw
  divisionFromNormSq := schema.canonicalIdealAlgebraization.divisionFromNormSq
  externalHurwitzCompatibility :=
    schema.canonicalIdealAlgebraization.externalHurwitzCompatibility

def S6ResearchSchema.toHurwitzStopSeed
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : HurwitzStopSeed X :=
  hurwitzStopSeedOf (schema := schema.toHurwitzUpgradeSchema) X

theorem S6ResearchSchema.toOpenProofObligations_eq
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    schema.toOpenProofObligations X =
      hurwitzOpenProofObligations schema.toHurwitzUpgradeSchema X := by
  rfl

theorem S6ResearchSchema.toHurwitzStopSeed_schema
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (schema.toHurwitzStopSeed X).schema = schema.toHurwitzUpgradeSchema := by
  rfl

theorem S6ResearchSchema.toHurwitzStopSeed_openProofObligations
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (schema.toHurwitzStopSeed X).openProofObligations =
      schema.toOpenProofObligations X := by
  rfl

def S6ResearchSchema.ResearchReady
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  OnticPrimacyTheorem X ∧
    PrenumericSectorTheorem X ∧
    ScalarAxisStatusSeparationTheorem X ∧
    (schema.toConjectureLayer X).octonionicIdeal ∧
    (schema.toConjectureLayer X).approximantProjection ∧
    (schema.toConjectureLayer X).cayleyDicksonLift

theorem researchReady_of_s6_theorem_layer
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (hConj : (schema.toConjectureLayer X).octonionicIdeal ∧
        (schema.toConjectureLayer X).approximantProjection ∧
        (schema.toConjectureLayer X).cayleyDicksonLift) :
    schema.ResearchReady X := by
  refine ⟨?_, ?_, ?_, hConj.1, hConj.2.1, hConj.2.2⟩
  · exact (s6_theorem_layer X).onticPrimacy
  · exact (s6_theorem_layer X).prenumericSector
  · exact (s6_theorem_layer X).scalarAxisStatusSeparation

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
