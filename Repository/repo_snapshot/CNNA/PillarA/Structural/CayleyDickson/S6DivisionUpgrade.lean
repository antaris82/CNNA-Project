import CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade
import CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold

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

structure DivisionBridgeCandidate
    (X : CayleyDicksonSource Cell T) : Prop where
  canonicalTriadicMultiplication : CanonicalTriadicMultiplicationCandidate X
  dualCompatibleConjugation : DualCompatibleConjugationCandidate
  diagonalNormUpgrade : DiagonalNormSqUpgradeCandidate X
  alternativeScaffold : AlternativeLawScaffoldCandidate X

theorem divisionBridgeCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    DivisionBridgeCandidate X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cayleyDickson_seed_canonicalTriadicMultiplication X
  · exact cayleyDickson_seed_dualCompatibleConjugation X
  · exact diagonalNormSqUpgradeCandidate_closed X
  · exact alternativeLawScaffoldCandidate_closed X

structure DivisionUpgradeSeed
    (X : CayleyDicksonSource Cell T) where
  normUpgrade : NormUpgradeSeed X
  normUpgrade_eq : normUpgrade = normUpgradeSeedOf X
  alternativeScaffold : AlternativeLawScaffoldSeed X
  alternativeScaffold_eq : alternativeScaffold = alternativeLawScaffoldSeedOf X
  bridge : DivisionBridgeCandidate X

def divisionUpgradeSeedOf
    (X : CayleyDicksonSource Cell T) :
    DivisionUpgradeSeed X where
  normUpgrade := normUpgradeSeedOf X
  normUpgrade_eq := rfl
  alternativeScaffold := alternativeLawScaffoldSeedOf X
  alternativeScaffold_eq := rfl
  bridge := divisionBridgeCandidate_closed X

structure DivisionUpgradeRemainingResearch where
  liftDiagonalToCanonicalNormSq : CayleyDicksonSource Cell T → Prop
  normSqMultiplicativeOnCanonicalProduct : CayleyDicksonSource Cell T → Prop
  canonicalNormSqImpliesDivision : CayleyDicksonSource Cell T → Prop

def DivisionFromNormSqUpgrade
    (remaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  DivisionBridgeCandidate X ∧
    remaining.liftDiagonalToCanonicalNormSq X ∧
    remaining.normSqMultiplicativeOnCanonicalProduct X ∧
    remaining.canonicalNormSqImpliesDivision X

theorem divisionFromNormSqUpgrade_iff
    (remaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    DivisionFromNormSqUpgrade remaining X ↔
      remaining.liftDiagonalToCanonicalNormSq X ∧
        remaining.normSqMultiplicativeOnCanonicalProduct X ∧
        remaining.canonicalNormSqImpliesDivision X := by
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · intro h
    exact ⟨divisionBridgeCandidate_closed X, h.1, h.2.1, h.2.2⟩

def CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (altRemaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T))
    (divRemaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T)) :
    CanonicalIdealAlgebraizationResearchSlot (Cell := Cell) (T := T) where
  idealHasCanonicalOctonionicAlgebra := remaining.idealHasCanonicalOctonionicAlgebra
  canonicalTriadicMultiplication := fun X => CanonicalTriadicMultiplicationCandidate X
  dualCompatibleConjugation := fun _ => DualCompatibleConjugationCandidate
  positiveDefiniteNormSq := fun X =>
    PositiveDefiniteNormSqFromDiagonal
      ({ liftDiagonalToCanonicalNormSq := divRemaining.liftDiagonalToCanonicalNormSq } :
        PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
      X
  alternativeLaw := fun X => AlternativeLawFromScaffold altRemaining X
  divisionFromNormSq := fun X => DivisionFromNormSqUpgrade divRemaining X
  externalHurwitzCompatibility := remaining.externalHurwitzCompatibility

def CayleyDicksonRemainingResearch.toResearchSchemaWithDivisionUpgrade
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (altRemaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T))
    (divRemaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T))
    (functorialSlot :
      FunctorialApproximantCompatibilityResearchSlot (Cell := Cell) (T := T))
    (regimeSlot : RegimeRecoveryResearchSlot (Cell := Cell) (T := T)) :
    S6ResearchSchema (Cell := Cell) (T := T) where
  canonicalIdealAlgebraization :=
    remaining.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade
      altRemaining divRemaining
  functorialApproximantCompatibility := functorialSlot
  regimeRecovery := regimeSlot

theorem divisionUpgradeSeed_bridge
    (X : CayleyDicksonSource Cell T) :
    DivisionBridgeCandidate X := by
  exact (divisionUpgradeSeedOf X).bridge

theorem toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade_canonicalTriadicMultiplication
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (altRemaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T))
    (divRemaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade
      altRemaining divRemaining).canonicalTriadicMultiplication X := by
  exact canonicalTriadicMultiplicationCandidate_of_octonionic X

theorem toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade_dualCompatibleConjugation
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (altRemaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T))
    (divRemaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade
      altRemaining divRemaining).dualCompatibleConjugation X := by
  exact dualCompatibleConjugationCandidate_closed

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
