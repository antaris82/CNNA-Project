import CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification

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

def AnalyticNormSqControl
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  0 ≤ MatrixNorm.Analytic.frobSq A ∧
    (MatrixNorm.Analytic.frobSq A = 0 ↔ A = 0) ∧
    (A ≠ 0 → 0 < MatrixNorm.Analytic.frobSq A)

theorem analyticNormSqControl_closed
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    AnalyticNormSqControl A := by
  refine ⟨?_, ?_, ?_⟩
  · exact MatrixNorm.Analytic.frobSq_nonneg A
  · exact MatrixNorm.Analytic.frobSq_eq_zero_iff A
  · intro hA
    exact MatrixNorm.Analytic.frobSq_pos_of_ne_zero A hA

def DiagonalNormSqUpgradeCandidate
    (X : CayleyDicksonSource Cell T) : Prop :=
  AnalyticNormSqControl X.schur.brightBrightSchur ∧
    AnalyticNormSqControl (triadicCenterMatrix X) ∧
    AnalyticNormSqControl X.schur.darkDarkSchur

theorem diagonalNormSqUpgradeCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    DiagonalNormSqUpgradeCandidate X := by
  refine ⟨?_, ?_, ?_⟩
  · exact analyticNormSqControl_closed X.schur.brightBrightSchur
  · exact analyticNormSqControl_closed (triadicCenterMatrix X)
  · exact analyticNormSqControl_closed X.schur.darkDarkSchur

theorem diagonalNormSqUpgradeCandidate_implies_nonneg
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X) :
    DiagonalNormSqNonnegCandidate X := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.1.1
  · exact h.2.1.1
  · exact h.2.2.1

theorem diagonalNormSqUpgradeCandidate_bright_eq_zero_iff
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X) :
    MatrixNorm.Analytic.frobSq X.schur.brightBrightSchur = 0 ↔
      X.schur.brightBrightSchur = 0 := by
  exact h.1.2.1

theorem diagonalNormSqUpgradeCandidate_center_eq_zero_iff
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X) :
    MatrixNorm.Analytic.frobSq (triadicCenterMatrix X) = 0 ↔
      triadicCenterMatrix X = 0 := by
  exact h.2.1.2.1

theorem diagonalNormSqUpgradeCandidate_dark_eq_zero_iff
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X) :
    MatrixNorm.Analytic.frobSq X.schur.darkDarkSchur = 0 ↔
      X.schur.darkDarkSchur = 0 := by
  exact h.2.2.2.1

theorem diagonalNormSqUpgradeCandidate_bright_pos_of_ne_zero
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X)
    (hA : X.schur.brightBrightSchur ≠ 0) :
    0 < MatrixNorm.Analytic.frobSq X.schur.brightBrightSchur := by
  exact h.1.2.2 hA

theorem diagonalNormSqUpgradeCandidate_center_pos_of_ne_zero
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X)
    (hA : triadicCenterMatrix X ≠ 0) :
    0 < MatrixNorm.Analytic.frobSq (triadicCenterMatrix X) := by
  exact h.2.1.2.2 hA

theorem diagonalNormSqUpgradeCandidate_dark_pos_of_ne_zero
    {X : CayleyDicksonSource Cell T}
    (h : DiagonalNormSqUpgradeCandidate X)
    (hA : X.schur.darkDarkSchur ≠ 0) :
    0 < MatrixNorm.Analytic.frobSq X.schur.darkDarkSchur := by
  exact h.2.2.2.2 hA

structure NormUpgradeSeed
    (X : CayleyDicksonSource Cell T) where
  cayleyDickson : CayleyDicksonIdentificationSeed X
  cayleyDickson_eq : cayleyDickson = cayleyDicksonIdentificationSeedOf X
  diagonalNormUpgrade : DiagonalNormSqUpgradeCandidate X

def normUpgradeSeedOf
    (X : CayleyDicksonSource Cell T) :
    NormUpgradeSeed X where
  cayleyDickson := cayleyDicksonIdentificationSeedOf X
  cayleyDickson_eq := rfl
  diagonalNormUpgrade := diagonalNormSqUpgradeCandidate_closed X

structure PositiveDefiniteNormSqRemainingResearch where
  liftDiagonalToCanonicalNormSq : CayleyDicksonSource Cell T → Prop

def PositiveDefiniteNormSqFromDiagonal
    (remaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  DiagonalNormSqUpgradeCandidate X ∧
    remaining.liftDiagonalToCanonicalNormSq X

theorem positiveDefiniteNormSqFromDiagonal_iff
    (remaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    PositiveDefiniteNormSqFromDiagonal remaining X ↔
      remaining.liftDiagonalToCanonicalNormSq X := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨diagonalNormSqUpgradeCandidate_closed X, h⟩

def CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (normRemaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T)) :
    CanonicalIdealAlgebraizationResearchSlot (Cell := Cell) (T := T) where
  idealHasCanonicalOctonionicAlgebra := remaining.idealHasCanonicalOctonionicAlgebra
  canonicalTriadicMultiplication :=
    fun X => CanonicalTriadicMultiplicationCandidate X
  dualCompatibleConjugation :=
    fun _ => DualCompatibleConjugationCandidate
  positiveDefiniteNormSq :=
    PositiveDefiniteNormSqFromDiagonal normRemaining
  alternativeLaw := remaining.alternativeLaw
  divisionFromNormSq := remaining.divisionFromNormSq
  externalHurwitzCompatibility := remaining.externalHurwitzCompatibility

def CayleyDicksonRemainingResearch.toResearchSchemaWithNormUpgrade
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (normRemaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
    (functorialSlot :
      FunctorialApproximantCompatibilityResearchSlot (Cell := Cell) (T := T))
    (regimeSlot : RegimeRecoveryResearchSlot (Cell := Cell) (T := T)) :
    S6ResearchSchema (Cell := Cell) (T := T) where
  canonicalIdealAlgebraization :=
    remaining.toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade normRemaining
  functorialApproximantCompatibility := functorialSlot
  regimeRecovery := regimeSlot

theorem normUpgradeSeed_canonicalTriadicMultiplication
    (X : CayleyDicksonSource Cell T) :
    CanonicalTriadicMultiplicationCandidate X := by
  exact (normUpgradeSeedOf X).cayleyDickson.canonicalTriadicMultiplication

theorem normUpgradeSeed_dualCompatibleConjugation
    (X : CayleyDicksonSource Cell T) :
    DualCompatibleConjugationCandidate := by
  exact (normUpgradeSeedOf X).cayleyDickson.dualCompatibleConjugation

theorem normUpgradeSeed_diagonalNormUpgrade
    (X : CayleyDicksonSource Cell T) :
    DiagonalNormSqUpgradeCandidate X := by
  exact (normUpgradeSeedOf X).diagonalNormUpgrade

theorem toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade_positiveDefiniteNormSq
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (normRemaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade normRemaining).positiveDefiniteNormSq X ↔
      normRemaining.liftDiagonalToCanonicalNormSq X := by
  exact positiveDefiniteNormSqFromDiagonal_iff normRemaining X

theorem toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade_canonicalTriadicMultiplication
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (normRemaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade normRemaining).canonicalTriadicMultiplication X := by
  exact canonicalTriadicMultiplicationCandidate_of_octonionic X

theorem toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade_dualCompatibleConjugation
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (normRemaining : PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlotWithNormUpgrade normRemaining).dualCompatibleConjugation X := by
  exact dualCompatibleConjugationCandidate_closed

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
