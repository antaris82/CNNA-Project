import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate
import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart

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

namespace CanonicalBlockTuple

variable (X : CayleyDicksonSource Cell T)

/--
Star-derived norm-square contribution of the bright-bright block.
By the comparison theorem below, this agrees extensionally with the analytic Frobenius square,
but the primary definition now comes from the carrier-level involution.
-/
def leftLeftNormSq
    (a : TriadicOuterBlock X .left .left) : ℝ :=
  leftLeftScalarPart X a

/--
Star-derived norm-square contribution of the bright-dark block.
-/
def leftRightNormSq
    (a : TriadicOuterBlock X .left .right) : ℝ :=
  leftRightScalarPart X a

/--
Star-derived norm-square contribution of the interface block.
-/
def centerNormSq
    (c : TriadicCenterBlock X) : ℝ :=
  centerScalarPart X c

/--
Star-derived norm-square contribution of the dark-bright block.
-/
def rightLeftNormSq
    (a : TriadicOuterBlock X .right .left) : ℝ :=
  rightLeftScalarPart X a

/--
Star-derived norm-square contribution of the dark-dark block.
-/
def rightRightNormSq
    (a : TriadicOuterBlock X .right .right) : ℝ :=
  rightRightScalarPart X a

/--
Star-derived norm-square on the common canonical carrier. The old Frobenius-sum surface is now
only a comparison theorem, not the defining source of Slot 2.
-/
def normSq (a : CanonicalBlockTuple X) : ℝ :=
  leftLeftNormSq X a.leftLeft +
    leftRightNormSq X a.leftRight +
    centerNormSq X a.center +
    rightLeftNormSq X a.rightLeft +
    rightRightNormSq X a.rightRight

@[simp] theorem zero_leftLeft :
    (0 : CanonicalBlockTuple X).leftLeft = 0 := by
  rfl

@[simp] theorem zero_leftRight :
    (0 : CanonicalBlockTuple X).leftRight = 0 := by
  rfl

@[simp] theorem zero_center :
    (0 : CanonicalBlockTuple X).center = 0 := by
  rfl

@[simp] theorem zero_rightLeft :
    (0 : CanonicalBlockTuple X).rightLeft = 0 := by
  rfl

@[simp] theorem zero_rightRight :
    (0 : CanonicalBlockTuple X).rightRight = 0 := by
  rfl

@[simp] theorem leftLeftNormSq_eq_frobSq
    (a : TriadicOuterBlock X .left .left) :
    leftLeftNormSq X a =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a := by
  exact leftLeftScalarPart_eq_frobSq X a

@[simp] theorem leftRightNormSq_eq_frobSqRect
    (a : TriadicOuterBlock X .left .right) :
    leftRightNormSq X a =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) a := by
  exact leftRightScalarPart_eq_frobSqRect X a

@[simp] theorem centerNormSq_eq_frobSq
    (c : TriadicCenterBlock X) :
    centerNormSq X c =
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) c := by
  exact centerScalarPart_eq_frobSq X c

@[simp] theorem rightLeftNormSq_eq_frobSqRect
    (a : TriadicOuterBlock X .right .left) :
    rightLeftNormSq X a =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) a := by
  exact rightLeftScalarPart_eq_frobSqRect X a

@[simp] theorem rightRightNormSq_eq_frobSq
    (a : TriadicOuterBlock X .right .right) :
    rightRightNormSq X a =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a := by
  exact rightRightScalarPart_eq_frobSq X a

@[simp] theorem leftLeftNormSq_zero :
    leftLeftNormSq X (0 : TriadicOuterBlock X .left .left) = 0 := by
  rw [leftLeftNormSq_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq]

@[simp] theorem leftRightNormSq_zero :
    leftRightNormSq X (0 : TriadicOuterBlock X .left .right) = 0 := by
  rw [leftRightNormSq_eq_frobSqRect]
  simp [MatrixNorm.Analytic.frobSqRect]

@[simp] theorem centerNormSq_zero :
    centerNormSq X (0 : TriadicCenterBlock X) = 0 := by
  rw [centerNormSq_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq]

@[simp] theorem rightLeftNormSq_zero :
    rightLeftNormSq X (0 : TriadicOuterBlock X .right .left) = 0 := by
  rw [rightLeftNormSq_eq_frobSqRect]
  simp [MatrixNorm.Analytic.frobSqRect]

@[simp] theorem rightRightNormSq_zero :
    rightRightNormSq X (0 : TriadicOuterBlock X .right .right) = 0 := by
  rw [rightRightNormSq_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq]

/-- Comparison theorem: the new star-derived Slot-2 norm agrees with the old Frobenius sum. -/
theorem normSq_eq_frobeniusSum
    (a : CanonicalBlockTuple X) :
    normSq X a =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a.leftLeft +
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a.leftRight +
        MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) a.center +
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a.rightLeft +
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a.rightRight := by
  unfold normSq
  rw [leftLeftNormSq_eq_frobSq,
    leftRightNormSq_eq_frobSqRect,
    centerNormSq_eq_frobSq,
    rightLeftNormSq_eq_frobSqRect,
    rightRightNormSq_eq_frobSq]

theorem normSq_nonneg (a : CanonicalBlockTuple X) :
    0 ≤ normSq X a := by
  have hLL : 0 ≤ leftLeftNormSq X a.leftLeft := by
    rw [leftLeftNormSq_eq_frobSq]
    exact MatrixNorm.Analytic.frobSq_nonneg (ι := X.schur.brightBoundaryVertex) a.leftLeft
  have hLR : 0 ≤ leftRightNormSq X a.leftRight := by
    rw [leftRightNormSq_eq_frobSqRect]
    exact MatrixNorm.Analytic.frobSqRect_nonneg
      (ι := X.schur.brightBoundaryVertex)
      (κ := X.schur.darkBoundaryVertex)
      a.leftRight
  have hC : 0 ≤ centerNormSq X a.center := by
    rw [centerNormSq_eq_frobSq]
    exact MatrixNorm.Analytic.frobSq_nonneg (ι := X.schur.interfaceBoundaryVertex) a.center
  have hRL : 0 ≤ rightLeftNormSq X a.rightLeft := by
    rw [rightLeftNormSq_eq_frobSqRect]
    exact MatrixNorm.Analytic.frobSqRect_nonneg
      (ι := X.schur.darkBoundaryVertex)
      (κ := X.schur.brightBoundaryVertex)
      a.rightLeft
  have hRR : 0 ≤ rightRightNormSq X a.rightRight := by
    rw [rightRightNormSq_eq_frobSq]
    exact MatrixNorm.Analytic.frobSq_nonneg (ι := X.schur.darkBoundaryVertex) a.rightRight
  unfold normSq
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hLL hLR) hC) hRL) hRR

theorem normSq_zero :
    normSq X (0 : CanonicalBlockTuple X) = 0 := by
  unfold normSq
  rw [leftLeftNormSq_eq_frobSq,
    leftRightNormSq_eq_frobSqRect,
    centerNormSq_eq_frobSq,
    rightLeftNormSq_eq_frobSqRect,
    rightRightNormSq_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq, MatrixNorm.Analytic.frobSqRect_zero]

theorem normSq_embedOuter_left_left
    (a : TriadicOuterBlock X .left .left) :
    normSq X (embedOuter X .left .left a) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a := by
  unfold normSq CanonicalBlockTuple.embedOuter
  rw [leftRightNormSq_zero, centerNormSq_zero, rightLeftNormSq_zero, rightRightNormSq_zero]
  rw [leftLeftNormSq_eq_frobSq]
  simp

theorem normSq_embedOuter_left_right
    (a : TriadicOuterBlock X .left .right) :
    normSq X (embedOuter X .left .right a) =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) a := by
  unfold normSq CanonicalBlockTuple.embedOuter
  rw [leftLeftNormSq_zero, centerNormSq_zero, rightLeftNormSq_zero, rightRightNormSq_zero]
  rw [leftRightNormSq_eq_frobSqRect]
  simp

theorem normSq_embedCenter
    (c : TriadicCenterBlock X) :
    normSq X (embedCenter X c) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) c := by
  unfold normSq CanonicalBlockTuple.embedCenter
  rw [leftLeftNormSq_zero, leftRightNormSq_zero, rightLeftNormSq_zero, rightRightNormSq_zero]
  rw [centerNormSq_eq_frobSq]
  simp

theorem normSq_embedOuter_right_left
    (a : TriadicOuterBlock X .right .left) :
    normSq X (embedOuter X .right .left a) =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) a := by
  unfold normSq CanonicalBlockTuple.embedOuter
  rw [leftLeftNormSq_zero, leftRightNormSq_zero, centerNormSq_zero, rightRightNormSq_zero]
  rw [rightLeftNormSq_eq_frobSqRect]
  simp

theorem normSq_embedOuter_right_right
    (a : TriadicOuterBlock X .right .right) :
    normSq X (embedOuter X .right .right a) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a := by
  unfold normSq CanonicalBlockTuple.embedOuter
  rw [leftLeftNormSq_zero, leftRightNormSq_zero, centerNormSq_zero, rightLeftNormSq_zero]
  rw [rightRightNormSq_eq_frobSq]
  simp

end CanonicalBlockTuple

theorem canonicalDiagonalNormSqLift_of_canonicalNormSq
    (X : CayleyDicksonSource Cell T) :
    CanonicalDiagonalNormSqLift X (CanonicalBlockTuple.normSq X) := by
  constructor
  · simpa using
      (CanonicalBlockTuple.normSq_embedOuter_left_left X X.schur.brightBrightSchur)
  constructor
  · simpa [CanonicalBlockTuple.centerNormSq] using
      (CanonicalBlockTuple.normSq_embedCenter X (triadicCenterMatrix X))
  · simpa using
      (CanonicalBlockTuple.normSq_embedOuter_right_right X X.schur.darkDarkSchur)

structure CanonicalFixedNormSqCandidate
    (X : CayleyDicksonSource Cell T) where
  normSqMultiplicativeOnCanonicalProduct :
    ∀ a b : CanonicalBlockTuple X,
      CanonicalBlockTuple.normSq X (CanonicalBlockTuple.mul X a b) =
        CanonicalBlockTuple.normSq X a * CanonicalBlockTuple.normSq X b

def canonicalNormSqCandidateOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    CanonicalNormSqCandidate X where
  normSq := CanonicalBlockTuple.normSq X
  liftDiagonalToCanonicalNormSq :=
    canonicalDiagonalNormSqLift_of_canonicalNormSq X
  normSqMultiplicativeOnCanonicalProduct := by
    intro a b
    exact h.normSqMultiplicativeOnCanonicalProduct a b

def canonicalFixedNormSqBoundaryOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    SchurBlockNormSqMultiplicativityBoundary X :=
  canonicalNormSqBoundaryOf X (canonicalNormSqCandidateOf X h)

def CanonicalFixedNormSqMultiplicativityFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (CanonicalFixedNormSqCandidate X)

theorem canonicalFixedNormSqMultiplicativityFrontier_implies_canonicalNormSqFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqMultiplicativityFrontier
      (Cell := Cell) (T := T) X) :
    CanonicalNormSqMultiplicativityFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqCandidateOf X witness⟩

theorem canonicalFixedNormSqMultiplicativityFrontier_implies_slot2Boundary
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqMultiplicativityFrontier
      (Cell := Cell) (T := T) X) :
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X := by
  exact canonicalNormSqMultiplicativityFrontier_implies_slot2Boundary X
    (canonicalFixedNormSqMultiplicativityFrontier_implies_canonicalNormSqFrontier X h)

theorem canonicalFixedNormSqMultiplicativityFrontier_implies_slot2Frontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqMultiplicativityFrontier
      (Cell := Cell) (T := T) X) :
    SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X := by
  exact canonicalNormSqMultiplicativityFrontier_implies_slot2Frontier X
    (canonicalFixedNormSqMultiplicativityFrontier_implies_canonicalNormSqFrontier X h)

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
