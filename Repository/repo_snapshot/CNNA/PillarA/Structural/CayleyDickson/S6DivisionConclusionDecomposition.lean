import CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure

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

/--
Step 2a of the final Phase-I frontier: the already closed scaffold together with
(1) the lift from diagonal control to the canonical norm square and
(2) multiplicativity of that canonical norm square on the canonical product.
-/
def SchurBlockNormSqMultiplicativityFrontier
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  NormSqMultiplicativityScaffoldCandidate X ∧
    normRemaining.liftDiagonalToCanonicalNormSq X ∧
    normRemaining.normSqMultiplicativeOnCanonicalProduct X

/--
Step 2b of the final Phase-I frontier: once the canonical norm square has been
constructed and made multiplicative, the remaining division step is the logical
no-zero-divisors consequence packaged as a separate frontier.
-/
def DivisionFromNormSqLogicFrontier
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  remaining.canonicalNormSqImpliesDivision X

theorem schurBlockNormSqMultiplicativityFrontier_eq
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    SchurBlockNormSqMultiplicativityFrontier normRemaining X ↔
      NormSqMultiplicativityFrontier normRemaining X := by
  rfl

theorem divisionFromNormSqLogicFrontier_eq
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    DivisionFromNormSqLogicFrontier remaining X ↔
      remaining.canonicalNormSqImpliesDivision X := by
  rfl

theorem divisionConclusionFrontier_iff_two_step
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionFrontier normRemaining remaining X ↔
      SchurBlockNormSqMultiplicativityFrontier normRemaining X ∧
        DivisionFromNormSqLogicFrontier remaining X := by
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2⟩
  · intro h
    exact ⟨divisionConclusionScaffoldCandidate_closed X, h.1, h.2⟩

theorem divisionConclusionFrontier_implies_two_step
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : DivisionConclusionFrontier normRemaining remaining X) :
    SchurBlockNormSqMultiplicativityFrontier normRemaining X ∧
      DivisionFromNormSqLogicFrontier remaining X := by
  exact (divisionConclusionFrontier_iff_two_step normRemaining remaining X).mp h

theorem two_step_implies_divisionConclusionFrontier
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : SchurBlockNormSqMultiplicativityFrontier normRemaining X ∧
      DivisionFromNormSqLogicFrontier remaining X) :
    DivisionConclusionFrontier normRemaining remaining X := by
  exact (divisionConclusionFrontier_iff_two_step normRemaining remaining X).mpr h

theorem schurBlockNormSqMultiplicativityFrontier_implies_positiveDefiniteNormSqFrontier
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : SchurBlockNormSqMultiplicativityFrontier normRemaining X) :
    PositiveDefiniteNormSqFrontier
      (normRemaining.toPositiveDefiniteNormSqLiftResearch) X := by
  exact normSqMultiplicativityFrontier_implies_positiveDefiniteNormSqFrontier
    normRemaining X h

theorem schurBlockNormSqMultiplicativityFrontier_implies_fromDiagonal
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : SchurBlockNormSqMultiplicativityFrontier normRemaining X) :
    PositiveDefiniteNormSqFromDiagonal
      ({ liftDiagonalToCanonicalNormSq := normRemaining.liftDiagonalToCanonicalNormSq } :
        PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T)) X := by
  exact normSqMultiplicativityFrontier_implies_positiveDefiniteNormSqFromDiagonal
    normRemaining X h

theorem divisionConclusionFrontier_iff_three_open_slots
    (normRemaining : NormSqMultiplicativityRemainingResearch
      (Cell := Cell) (T := T))
    (remaining : DivisionConclusionRemainingResearch
      (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionFrontier normRemaining remaining X ↔
      normRemaining.liftDiagonalToCanonicalNormSq X ∧
      normRemaining.normSqMultiplicativeOnCanonicalProduct X ∧
      DivisionFromNormSqLogicFrontier remaining X := by
  simpa [DivisionFromNormSqLogicFrontier] using
    (divisionConclusionFrontier_iff normRemaining remaining X)

def CanonicalIdealAlgebraizationProgram.PhaseITwoStepFrontier
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  AlternativeLawFromScaffold program.alternativeRemaining X ∧
    SchurBlockNormSqMultiplicativityFrontier
      (program.toNormSqMultiplicativityRemainingResearch) X ∧
    DivisionFromNormSqLogicFrontier
      (program.toDivisionConclusionRemainingResearch) X

theorem CanonicalIdealAlgebraizationProgram.phaseICompactFrontier_iff_two_step
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    program.PhaseICompactFrontier X ↔ program.PhaseITwoStepFrontier X := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  · intro h
    refine ⟨h.1, ?_⟩
    exact two_step_implies_divisionConclusionFrontier
      (program.toNormSqMultiplicativityRemainingResearch)
      (program.toDivisionConclusionRemainingResearch)
      X
      ⟨h.2.1, h.2.2⟩

theorem CanonicalIdealAlgebraizationProgram.phaseIClosed_iff_two_step
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    program.PhaseIClosed X ↔ program.PhaseITwoStepFrontier X := by
  constructor
  · intro h
    have hCompact :=
      (CanonicalIdealAlgebraizationProgram.phaseIClosed_iff_compactFrontier program X).mp h
    exact (CanonicalIdealAlgebraizationProgram.phaseICompactFrontier_iff_two_step program X).mp hCompact
  · intro h
    have hCompact :=
      (CanonicalIdealAlgebraizationProgram.phaseICompactFrontier_iff_two_step program X).mpr h
    exact (CanonicalIdealAlgebraizationProgram.phaseIClosed_iff_compactFrontier program X).mpr hCompact

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
