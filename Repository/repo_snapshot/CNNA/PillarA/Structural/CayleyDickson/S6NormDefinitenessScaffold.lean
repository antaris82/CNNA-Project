import CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade

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

structure PositiveDefiniteNormSqScaffoldCandidate
    (X : CayleyDicksonSource Cell T) : Prop where
  diagonalNormUpgrade : DiagonalNormSqUpgradeCandidate X
  brightEqZeroIff :
    MatrixNorm.Analytic.frobSq X.schur.brightBrightSchur = 0 ↔
      X.schur.brightBrightSchur = 0
  centerEqZeroIff :
    MatrixNorm.Analytic.frobSq (triadicCenterMatrix X) = 0 ↔
      triadicCenterMatrix X = 0
  darkEqZeroIff :
    MatrixNorm.Analytic.frobSq X.schur.darkDarkSchur = 0 ↔
      X.schur.darkDarkSchur = 0
  brightPosOfNeZero :
    X.schur.brightBrightSchur ≠ 0 →
      0 < MatrixNorm.Analytic.frobSq X.schur.brightBrightSchur
  centerPosOfNeZero :
    triadicCenterMatrix X ≠ 0 →
      0 < MatrixNorm.Analytic.frobSq (triadicCenterMatrix X)
  darkPosOfNeZero :
    X.schur.darkDarkSchur ≠ 0 →
      0 < MatrixNorm.Analytic.frobSq X.schur.darkDarkSchur

theorem positiveDefiniteNormSqScaffoldCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    PositiveDefiniteNormSqScaffoldCandidate X := by
  let hDiag := diagonalNormSqUpgradeCandidate_closed X
  refine ⟨hDiag, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact diagonalNormSqUpgradeCandidate_bright_eq_zero_iff hDiag
  · exact diagonalNormSqUpgradeCandidate_center_eq_zero_iff hDiag
  · exact diagonalNormSqUpgradeCandidate_dark_eq_zero_iff hDiag
  · exact diagonalNormSqUpgradeCandidate_bright_pos_of_ne_zero hDiag
  · exact diagonalNormSqUpgradeCandidate_center_pos_of_ne_zero hDiag
  · exact diagonalNormSqUpgradeCandidate_dark_pos_of_ne_zero hDiag

structure PositiveDefiniteNormSqScaffoldSeed
    (X : CayleyDicksonSource Cell T) where
  normUpgrade : NormUpgradeSeed X
  normUpgrade_eq : normUpgrade = normUpgradeSeedOf X
  scaffold : PositiveDefiniteNormSqScaffoldCandidate X

def positiveDefiniteNormSqScaffoldSeedOf
    (X : CayleyDicksonSource Cell T) :
    PositiveDefiniteNormSqScaffoldSeed X where
  normUpgrade := normUpgradeSeedOf X
  normUpgrade_eq := rfl
  scaffold := positiveDefiniteNormSqScaffoldCandidate_closed X

theorem positiveDefiniteNormSqScaffoldCandidate_implies_nonneg
    {X : CayleyDicksonSource Cell T}
    (h : PositiveDefiniteNormSqScaffoldCandidate X) :
    DiagonalNormSqNonnegCandidate X := by
  exact diagonalNormSqUpgradeCandidate_implies_nonneg h.diagonalNormUpgrade

structure PositiveDefiniteNormSqLiftResearch where
  liftDiagonalToCanonicalNormSq : CayleyDicksonSource Cell T → Prop

def PositiveDefiniteNormSqFrontier
    (remaining : PositiveDefiniteNormSqLiftResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  PositiveDefiniteNormSqScaffoldCandidate X ∧
    remaining.liftDiagonalToCanonicalNormSq X

theorem positiveDefiniteNormSqFrontier_iff
    (remaining : PositiveDefiniteNormSqLiftResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    PositiveDefiniteNormSqFrontier remaining X ↔
      remaining.liftDiagonalToCanonicalNormSq X := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨positiveDefiniteNormSqScaffoldCandidate_closed X, h⟩

theorem positiveDefiniteNormSqFrontier_implies_fromDiagonal
    (remaining : PositiveDefiniteNormSqLiftResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : PositiveDefiniteNormSqFrontier remaining X) :
    PositiveDefiniteNormSqFromDiagonal
      ({ liftDiagonalToCanonicalNormSq := remaining.liftDiagonalToCanonicalNormSq } :
        PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
      X := by
  exact ⟨h.1.diagonalNormUpgrade, h.2⟩

theorem positiveDefiniteNormSqFromDiagonal_implies_frontier
    (remaining : PositiveDefiniteNormSqLiftResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : PositiveDefiniteNormSqFromDiagonal
      ({ liftDiagonalToCanonicalNormSq := remaining.liftDiagonalToCanonicalNormSq } :
        PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
      X) :
    PositiveDefiniteNormSqFrontier remaining X := by
  exact ⟨positiveDefiniteNormSqScaffoldCandidate_closed X, h.2⟩

theorem positiveDefiniteNormSqFrontier_iff_fromDiagonal
    (remaining : PositiveDefiniteNormSqLiftResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    PositiveDefiniteNormSqFrontier remaining X ↔
      PositiveDefiniteNormSqFromDiagonal
        ({ liftDiagonalToCanonicalNormSq := remaining.liftDiagonalToCanonicalNormSq } :
          PositiveDefiniteNormSqRemainingResearch (Cell := Cell) (T := T))
        X := by
  constructor
  · intro h
    exact positiveDefiniteNormSqFrontier_implies_fromDiagonal remaining X h
  · intro h
    exact positiveDefiniteNormSqFromDiagonal_implies_frontier remaining X h

theorem positiveDefiniteNormSqScaffoldSeed_scaffold
    (X : CayleyDicksonSource Cell T) :
    PositiveDefiniteNormSqScaffoldCandidate X := by
  exact (positiveDefiniteNormSqScaffoldSeedOf X).scaffold

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
