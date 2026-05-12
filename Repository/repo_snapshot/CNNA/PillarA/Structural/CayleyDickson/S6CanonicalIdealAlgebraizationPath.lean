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

structure CanonicalIdealAlgebraizationPath
    (X : CayleyDicksonSource Cell T) where
  divisionUpgrade : DivisionUpgradeSeed X
  divisionUpgrade_eq : divisionUpgrade = divisionUpgradeSeedOf X
  canonicalTriadicMultiplication : CanonicalTriadicMultiplicationCandidate X
  dualCompatibleConjugation : DualCompatibleConjugationCandidate
  diagonalNormUpgrade : DiagonalNormSqUpgradeCandidate X
  alternativeScaffold : AlternativeLawScaffoldCandidate X

def canonicalIdealAlgebraizationPathOf
    (X : CayleyDicksonSource Cell T) :
    CanonicalIdealAlgebraizationPath X where
  divisionUpgrade := divisionUpgradeSeedOf X
  divisionUpgrade_eq := rfl
  canonicalTriadicMultiplication :=
    cayleyDickson_seed_canonicalTriadicMultiplication X
  dualCompatibleConjugation :=
    cayleyDickson_seed_dualCompatibleConjugation X
  diagonalNormUpgrade :=
    diagonalNormSqUpgradeCandidate_closed X
  alternativeScaffold :=
    alternativeLawScaffoldCandidate_closed X

def CanonicalIdealAlgebraizationPhaseIReady
    (X : CayleyDicksonSource Cell T) : Prop :=
  CanonicalTriadicMultiplicationCandidate X ∧
    DualCompatibleConjugationCandidate ∧
    DiagonalNormSqUpgradeCandidate X ∧
    AlternativeLawScaffoldCandidate X

theorem canonicalIdealAlgebraizationPhaseIReady_closed
    (X : CayleyDicksonSource Cell T) :
    CanonicalIdealAlgebraizationPhaseIReady X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cayleyDickson_seed_canonicalTriadicMultiplication X
  · exact cayleyDickson_seed_dualCompatibleConjugation X
  · exact diagonalNormSqUpgradeCandidate_closed X
  · exact alternativeLawScaffoldCandidate_closed X

structure CanonicalIdealAlgebraizationProgram where
  cayleyDicksonRemaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T)
  alternativeRemaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T)
  divisionRemaining : DivisionUpgradeRemainingResearch (Cell := Cell) (T := T)
  functorialSlot :
    FunctorialApproximantCompatibilityResearchSlot (Cell := Cell) (T := T)
  regimeSlot : RegimeRecoveryResearchSlot (Cell := Cell) (T := T)

def CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T)) :
    CanonicalIdealAlgebraizationResearchSlot (Cell := Cell) (T := T) :=
  CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade
    program.cayleyDicksonRemaining
    program.alternativeRemaining
    program.divisionRemaining

def CanonicalIdealAlgebraizationProgram.toResearchSchema
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T)) :
    S6ResearchSchema (Cell := Cell) (T := T) :=
  CayleyDicksonRemainingResearch.toResearchSchemaWithDivisionUpgrade
    program.cayleyDicksonRemaining
    program.alternativeRemaining
    program.divisionRemaining
    program.functorialSlot
    program.regimeSlot

def CanonicalIdealAlgebraizationProgram.PhaseIClosed
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  (program.toCanonicalIdealAlgebraizationResearchSlot).canonicalTriadicMultiplication X ∧
    (program.toCanonicalIdealAlgebraizationResearchSlot).dualCompatibleConjugation X ∧
    (program.toCanonicalIdealAlgebraizationResearchSlot).positiveDefiniteNormSq X ∧
    (program.toCanonicalIdealAlgebraizationResearchSlot).alternativeLaw X ∧
    (program.toCanonicalIdealAlgebraizationResearchSlot).divisionFromNormSq X

theorem CanonicalIdealAlgebraizationProgram.phaseIClosed_iff
    (program : CanonicalIdealAlgebraizationProgram (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    program.PhaseIClosed X ↔
      PositiveDefiniteNormSqFromDiagonal
        ({ liftDiagonalToCanonicalNormSq :=
            program.divisionRemaining.liftDiagonalToCanonicalNormSq } :
          PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
        X ∧
      AlternativeLawFromScaffold program.alternativeRemaining X ∧
      DivisionFromNormSqUpgrade program.divisionRemaining X := by
  constructor
  · intro h
    have hNorm :
        PositiveDefiniteNormSqFromDiagonal
          ({ liftDiagonalToCanonicalNormSq :=
              program.divisionRemaining.liftDiagonalToCanonicalNormSq } :
            PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T)) X := by
      simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using h.2.2.1
    have hAlt : AlternativeLawFromScaffold program.alternativeRemaining X := by
      simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using h.2.2.2.1
    have hDiv : DivisionFromNormSqUpgrade program.divisionRemaining X := by
      simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using h.2.2.2.2
    exact ⟨hNorm, hAlt, hDiv⟩
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using (canonicalTriadicMultiplicationCandidate_of_octonionic X)
    · simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using (dualCompatibleConjugationCandidate_closed)
    · simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using h.1
    · simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using h.2.1
    · simpa [CanonicalIdealAlgebraizationProgram.toCanonicalIdealAlgebraizationResearchSlot,
        CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithDivisionUpgrade]
        using h.2.2

theorem canonicalIdealAlgebraizationPath_phaseIReady
    (X : CayleyDicksonSource Cell T) :
    CanonicalIdealAlgebraizationPhaseIReady X := by
  exact canonicalIdealAlgebraizationPhaseIReady_closed X

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
