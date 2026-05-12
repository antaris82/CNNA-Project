import CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold
import CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade

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

structure NormSqMultiplicativityScaffoldCandidate
    (X : CayleyDicksonSource Cell T) : Prop where
  divisionBridge : DivisionBridgeCandidate X
  positiveDefiniteNormSqScaffold : PositiveDefiniteNormSqScaffoldCandidate X

theorem normSqMultiplicativityScaffoldCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    NormSqMultiplicativityScaffoldCandidate X := by
  refine ⟨?_, ?_⟩
  · exact divisionBridgeCandidate_closed X
  · exact positiveDefiniteNormSqScaffoldCandidate_closed X

structure NormSqMultiplicativityScaffoldSeed
    (X : CayleyDicksonSource Cell T) where
  divisionUpgrade : DivisionUpgradeSeed X
  divisionUpgrade_eq : divisionUpgrade = divisionUpgradeSeedOf X
  normDefiniteness : PositiveDefiniteNormSqScaffoldSeed X
  normDefiniteness_eq :
    normDefiniteness = positiveDefiniteNormSqScaffoldSeedOf X
  scaffold : NormSqMultiplicativityScaffoldCandidate X

def normSqMultiplicativityScaffoldSeedOf
    (X : CayleyDicksonSource Cell T) :
    NormSqMultiplicativityScaffoldSeed X where
  divisionUpgrade := divisionUpgradeSeedOf X
  divisionUpgrade_eq := rfl
  normDefiniteness := positiveDefiniteNormSqScaffoldSeedOf X
  normDefiniteness_eq := rfl
  scaffold := normSqMultiplicativityScaffoldCandidate_closed X

structure NormSqMultiplicativityRemainingResearch where
  liftDiagonalToCanonicalNormSq : CayleyDicksonSource Cell T → Prop
  normSqMultiplicativeOnCanonicalProduct : CayleyDicksonSource Cell T → Prop

def NormSqMultiplicativityFrontier
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  NormSqMultiplicativityScaffoldCandidate X ∧
    remaining.liftDiagonalToCanonicalNormSq X ∧
    remaining.normSqMultiplicativeOnCanonicalProduct X

theorem normSqMultiplicativityFrontier_iff
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    NormSqMultiplicativityFrontier remaining X ↔
      remaining.liftDiagonalToCanonicalNormSq X ∧
        remaining.normSqMultiplicativeOnCanonicalProduct X := by
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2⟩
  · intro h
    exact ⟨normSqMultiplicativityScaffoldCandidate_closed X, h.1, h.2⟩

def NormSqMultiplicativityRemainingResearch.toPositiveDefiniteNormSqLiftResearch
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T)) :
    PositiveDefiniteNormSqLiftResearch (Cell := Cell) (T := T) where
  liftDiagonalToCanonicalNormSq := remaining.liftDiagonalToCanonicalNormSq

def NormSqMultiplicativityRemainingResearch.toDivisionUpgradeRemainingResearch
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (canonicalNormSqImpliesDivision : CayleyDicksonSource Cell T → Prop) :
    DivisionUpgradeRemainingResearch (Cell := Cell) (T := T) where
  liftDiagonalToCanonicalNormSq := remaining.liftDiagonalToCanonicalNormSq
  normSqMultiplicativeOnCanonicalProduct :=
    remaining.normSqMultiplicativeOnCanonicalProduct
  canonicalNormSqImpliesDivision := canonicalNormSqImpliesDivision

theorem normSqMultiplicativityFrontier_implies_positiveDefiniteNormSqFrontier
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : NormSqMultiplicativityFrontier remaining X) :
    PositiveDefiniteNormSqFrontier
      (remaining.toPositiveDefiniteNormSqLiftResearch) X := by
  exact ⟨h.1.positiveDefiniteNormSqScaffold, h.2.1⟩

theorem normSqMultiplicativityFrontier_implies_positiveDefiniteNormSqFromDiagonal
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : NormSqMultiplicativityFrontier remaining X) :
    PositiveDefiniteNormSqFromDiagonal
      ({ liftDiagonalToCanonicalNormSq := remaining.liftDiagonalToCanonicalNormSq } :
        PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
      X := by
  exact positiveDefiniteNormSqFrontier_implies_fromDiagonal
    (remaining.toPositiveDefiniteNormSqLiftResearch) X
    (normSqMultiplicativityFrontier_implies_positiveDefiniteNormSqFrontier
      remaining X h)

theorem normSqMultiplicativityFrontier_implies_divisionFromNormSqUpgrade
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (canonicalNormSqImpliesDivision : CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T)
    (hFrontier : NormSqMultiplicativityFrontier remaining X)
    (hDivision : canonicalNormSqImpliesDivision X) :
    DivisionFromNormSqUpgrade
      (remaining.toDivisionUpgradeRemainingResearch canonicalNormSqImpliesDivision)
      X := by
  exact ⟨hFrontier.1.divisionBridge, hFrontier.2.1, hFrontier.2.2, hDivision⟩

theorem divisionFromNormSqUpgrade_implies_normSqMultiplicativityFrontier
    (remaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (canonicalNormSqImpliesDivision : CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T)
    (h : DivisionFromNormSqUpgrade
      (remaining.toDivisionUpgradeRemainingResearch canonicalNormSqImpliesDivision)
      X) :
    NormSqMultiplicativityFrontier remaining X := by
  exact ⟨normSqMultiplicativityScaffoldCandidate_closed X, h.2.1, h.2.2.1⟩

theorem normSqMultiplicativityScaffoldSeed_scaffold
    (X : CayleyDicksonSource Cell T) :
    NormSqMultiplicativityScaffoldCandidate X := by
  exact (normSqMultiplicativityScaffoldSeedOf X).scaffold

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
