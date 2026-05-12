import CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold
import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath

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

structure DivisionConclusionScaffoldCandidate
    (X : CayleyDicksonSource Cell T) : Prop where
  normMultiplicativity : NormSqMultiplicativityScaffoldCandidate X
  phaseIReady : CanonicalIdealAlgebraizationPhaseIReady X

theorem divisionConclusionScaffoldCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionScaffoldCandidate X := by
  refine ⟨?_, ?_⟩
  · exact normSqMultiplicativityScaffoldCandidate_closed X
  · exact canonicalIdealAlgebraizationPhaseIReady_closed X

structure DivisionConclusionScaffoldSeed
    (X : CayleyDicksonSource Cell T) where
  normMultiplicativity : NormSqMultiplicativityScaffoldSeed X
  normMultiplicativity_eq :
    normMultiplicativity = normSqMultiplicativityScaffoldSeedOf X
  canonicalPath : CanonicalIdealAlgebraizationPath X
  canonicalPath_eq : canonicalPath = canonicalIdealAlgebraizationPathOf X
  scaffold : DivisionConclusionScaffoldCandidate X

def divisionConclusionScaffoldSeedOf
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionScaffoldSeed X where
  normMultiplicativity := normSqMultiplicativityScaffoldSeedOf X
  normMultiplicativity_eq := rfl
  canonicalPath := canonicalIdealAlgebraizationPathOf X
  canonicalPath_eq := rfl
  scaffold := divisionConclusionScaffoldCandidate_closed X

structure DivisionConclusionRemainingResearch where
  canonicalNormSqImpliesDivision : CayleyDicksonSource Cell T → Prop

def DivisionConclusionRemainingResearch.toDivisionUpgradeRemainingResearch
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T)) :
    DivisionUpgradeRemainingResearch (Cell := Cell) (T := T) where
  liftDiagonalToCanonicalNormSq := normRemaining.liftDiagonalToCanonicalNormSq
  normSqMultiplicativeOnCanonicalProduct :=
    normRemaining.normSqMultiplicativeOnCanonicalProduct
  canonicalNormSqImpliesDivision :=
    remaining.canonicalNormSqImpliesDivision

def DivisionConclusionFrontier
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  DivisionConclusionScaffoldCandidate X ∧
    NormSqMultiplicativityFrontier normRemaining X ∧
    remaining.canonicalNormSqImpliesDivision X

theorem divisionConclusionFrontier_iff
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionFrontier normRemaining remaining X ↔
      normRemaining.liftDiagonalToCanonicalNormSq X ∧
      normRemaining.normSqMultiplicativeOnCanonicalProduct X ∧
      remaining.canonicalNormSqImpliesDivision X := by
  constructor
  · intro h
    exact ⟨h.2.1.2.1, h.2.1.2.2, h.2.2⟩
  · intro h
    exact ⟨divisionConclusionScaffoldCandidate_closed X,
      ⟨normSqMultiplicativityScaffoldCandidate_closed X, h.1, h.2.1⟩,
      h.2.2⟩

theorem divisionConclusionFrontier_implies_divisionFromNormSqUpgrade
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : DivisionConclusionFrontier normRemaining remaining X) :
    DivisionFromNormSqUpgrade
      (remaining.toDivisionUpgradeRemainingResearch normRemaining)
      X := by
  exact normSqMultiplicativityFrontier_implies_divisionFromNormSqUpgrade
    normRemaining remaining.canonicalNormSqImpliesDivision X h.2.1 h.2.2

theorem divisionFromNormSqUpgrade_implies_divisionConclusionFrontier
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : DivisionFromNormSqUpgrade
      (remaining.toDivisionUpgradeRemainingResearch normRemaining)
      X) :
    DivisionConclusionFrontier normRemaining remaining X := by
  refine ⟨?_, ?_, ?_⟩
  · exact divisionConclusionScaffoldCandidate_closed X
  · exact divisionFromNormSqUpgrade_implies_normSqMultiplicativityFrontier
      normRemaining remaining.canonicalNormSqImpliesDivision X h
  · exact h.2.2.2

theorem divisionConclusionFrontier_iff_divisionFromNormSqUpgrade
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionFrontier normRemaining remaining X ↔
      DivisionFromNormSqUpgrade
        (remaining.toDivisionUpgradeRemainingResearch normRemaining)
        X := by
  constructor
  · intro h
    exact divisionConclusionFrontier_implies_divisionFromNormSqUpgrade
      normRemaining remaining X h
  · intro h
    exact divisionFromNormSqUpgrade_implies_divisionConclusionFrontier
      normRemaining remaining X h

theorem divisionConclusionFrontier_implies_phaseIReady
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : DivisionConclusionFrontier normRemaining remaining X) :
    CanonicalIdealAlgebraizationPhaseIReady X := by
  exact h.1.phaseIReady

theorem divisionConclusionScaffoldSeed_phaseIReady
    (X : CayleyDicksonSource Cell T) :
    CanonicalIdealAlgebraizationPhaseIReady X := by
  exact (divisionConclusionScaffoldSeedOf X).scaffold.phaseIReady

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
