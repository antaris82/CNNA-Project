import CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold

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

def CanonicalIdealAlgebraizationProgram.toNormSqMultiplicativityRemainingResearch
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T)) :
    NormSqMultiplicativityRemainingResearch (Cell := Cell) (T := T) where
  liftDiagonalToCanonicalNormSq :=
    program.divisionRemaining.liftDiagonalToCanonicalNormSq
  normSqMultiplicativeOnCanonicalProduct :=
    program.divisionRemaining.normSqMultiplicativeOnCanonicalProduct

def CanonicalIdealAlgebraizationProgram.toDivisionConclusionRemainingResearch
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T)) :
    DivisionConclusionRemainingResearch (Cell := Cell) (T := T) where
  canonicalNormSqImpliesDivision :=
    program.divisionRemaining.canonicalNormSqImpliesDivision

theorem CanonicalIdealAlgebraizationProgram.toDivisionUpgradeRemainingResearch_eq
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T)) :
    DivisionConclusionRemainingResearch.toDivisionUpgradeRemainingResearch
      (program.toDivisionConclusionRemainingResearch)
      (program.toNormSqMultiplicativityRemainingResearch) =
      program.divisionRemaining := by
  rfl

def CanonicalIdealAlgebraizationProgram.PhaseICompactFrontier
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  AlternativeLawFromScaffold program.alternativeRemaining X ∧
    DivisionConclusionFrontier
      (program.toNormSqMultiplicativityRemainingResearch)
      (program.toDivisionConclusionRemainingResearch)
      X

theorem CanonicalIdealAlgebraizationProgram.phaseIClosed_iff_compactFrontier
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    program.PhaseIClosed X ↔ program.PhaseICompactFrontier X := by
  constructor
  · intro h
    have hCore := (CanonicalIdealAlgebraizationProgram.phaseIClosed_iff program X).mp h
    have hAlt : AlternativeLawFromScaffold program.alternativeRemaining X :=
      hCore.2.1
    have hDiv : DivisionFromNormSqUpgrade
        program.divisionRemaining X :=
      hCore.2.2
    have hFrontier : DivisionConclusionFrontier
        (program.toNormSqMultiplicativityRemainingResearch)
        (program.toDivisionConclusionRemainingResearch)
        X := by
      simpa [CanonicalIdealAlgebraizationProgram.toDivisionUpgradeRemainingResearch_eq]
        using
          (divisionFromNormSqUpgrade_implies_divisionConclusionFrontier
            (program.toNormSqMultiplicativityRemainingResearch)
            (program.toDivisionConclusionRemainingResearch)
            X
            hDiv)
    exact ⟨hAlt, hFrontier⟩
  · intro h
    have hAlt : AlternativeLawFromScaffold program.alternativeRemaining X := h.1
    have hFrontier : DivisionConclusionFrontier
        (program.toNormSqMultiplicativityRemainingResearch)
        (program.toDivisionConclusionRemainingResearch)
        X := h.2
    have hDiv : DivisionFromNormSqUpgrade program.divisionRemaining X := by
      simpa [CanonicalIdealAlgebraizationProgram.toDivisionUpgradeRemainingResearch_eq]
        using
          (divisionConclusionFrontier_implies_divisionFromNormSqUpgrade
            (program.toNormSqMultiplicativityRemainingResearch)
            (program.toDivisionConclusionRemainingResearch)
            X
            hFrontier)
    have hLift :
        program.divisionRemaining.liftDiagonalToCanonicalNormSq X := by
      exact (divisionFromNormSqUpgrade_iff program.divisionRemaining X).mp hDiv |>.1
    have hNorm : PositiveDefiniteNormSqFromDiagonal
        ({ liftDiagonalToCanonicalNormSq :=
            program.divisionRemaining.liftDiagonalToCanonicalNormSq } :
          PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T)) X := by
      exact ⟨diagonalNormSqUpgradeCandidate_closed X, hLift⟩
    exact (CanonicalIdealAlgebraizationProgram.phaseIClosed_iff program X).mpr
      ⟨hNorm, hAlt, hDiv⟩

theorem CanonicalIdealAlgebraizationProgram.compactFrontier_implies_phaseIReady
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : program.PhaseICompactFrontier X) :
    CanonicalIdealAlgebraizationPhaseIReady X := by
  exact divisionConclusionFrontier_implies_phaseIReady
    (program.toNormSqMultiplicativityRemainingResearch)
    (program.toDivisionConclusionRemainingResearch)
    X
    h.2

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
