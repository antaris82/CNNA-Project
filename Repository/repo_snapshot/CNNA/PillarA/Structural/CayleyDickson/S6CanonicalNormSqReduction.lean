import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined

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

 theorem mul_embedOuter_left_left_left_left
    (a b : TriadicOuterBlock X .left .left) :
    mul X (embedOuter X .left .left a) (embedOuter X .left .left b) =
      embedOuter X .left .left (compose_left_left_left X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_left_left_left_right
    (a : TriadicOuterBlock X .left .left)
    (b : TriadicOuterBlock X .left .right) :
    mul X (embedOuter X .left .left a) (embedOuter X .left .right b) =
      embedOuter X .left .right (compose_left_left_right X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_left_right_right_left
    (a : TriadicOuterBlock X .left .right)
    (b : TriadicOuterBlock X .right .left) :
    mul X (embedOuter X .left .right a) (embedOuter X .right .left b) =
      embedOuter X .left .left (compose_left_right_left X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_left_right_right_right
    (a : TriadicOuterBlock X .left .right)
    (b : TriadicOuterBlock X .right .right) :
    mul X (embedOuter X .left .right a) (embedOuter X .right .right b) =
      embedOuter X .left .right (compose_left_right_right X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedCenter_center
    (a b : TriadicCenterBlock X) :
    mul X (embedCenter X a) (embedCenter X b) =
      embedCenter X (compose_center X a b) := by
  ext <;>
    simp [mul, embedCenter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_right_left_left_left
    (a : TriadicOuterBlock X .right .left)
    (b : TriadicOuterBlock X .left .left) :
    mul X (embedOuter X .right .left a) (embedOuter X .left .left b) =
      embedOuter X .right .left (compose_right_left_left X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_right_left_left_right
    (a : TriadicOuterBlock X .right .left)
    (b : TriadicOuterBlock X .left .right) :
    mul X (embedOuter X .right .left a) (embedOuter X .left .right b) =
      embedOuter X .right .right (compose_right_left_right X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_right_right_right_left
    (a : TriadicOuterBlock X .right .right)
    (b : TriadicOuterBlock X .right .left) :
    mul X (embedOuter X .right .right a) (embedOuter X .right .left b) =
      embedOuter X .right .left (compose_right_right_left X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

 theorem mul_embedOuter_right_right_right_right
    (a b : TriadicOuterBlock X .right .right) :
    mul X (embedOuter X .right .right a) (embedOuter X .right .right b) =
      embedOuter X .right .right (compose_right_right_right X a b) := by
  ext <;>
    simp [mul, embedOuter,
      compose_left_left_left, compose_left_right_left,
      compose_left_left_right, compose_left_right_right,
      compose_center,
      compose_right_left_left, compose_right_right_left,
      compose_right_left_right, compose_right_right_right]

end CanonicalBlockTuple

theorem canonicalFixedNormSqCandidate_forces_left_left_left_left
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a b : TriadicOuterBlock X .left .left) :
    MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
      (CanonicalBlockTuple.compose_left_left_left X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .left .left a)
    (CanonicalBlockTuple.embedOuter X .left .left b)
  calc
    MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
        (CanonicalBlockTuple.compose_left_left_left X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .left .left a)
            (CanonicalBlockTuple.embedOuter X .left .left b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_left_left_left_left X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_left_left X
            (CanonicalBlockTuple.compose_left_left_left X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .left a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .left b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
          MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_left_left,
            CanonicalBlockTuple.normSq_embedOuter_left_left]

 theorem canonicalFixedNormSqCandidate_forces_left_left_left_right
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a : TriadicOuterBlock X .left .left)
    (b : TriadicOuterBlock X .left .right) :
    MatrixNorm.Analytic.frobSqRect
      (ι := X.schur.brightBoundaryVertex)
      (κ := X.schur.darkBoundaryVertex)
      (CanonicalBlockTuple.compose_left_left_right X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .left .left a)
    (CanonicalBlockTuple.embedOuter X .left .right b)
  calc
    MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex)
        (CanonicalBlockTuple.compose_left_left_right X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .left .left a)
            (CanonicalBlockTuple.embedOuter X .left .right b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_left_left_left_right X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_left_right X
            (CanonicalBlockTuple.compose_left_left_right X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .left a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .right b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
          MatrixNorm.Analytic.frobSqRect
            (ι := X.schur.brightBoundaryVertex)
            (κ := X.schur.darkBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_left_left,
            CanonicalBlockTuple.normSq_embedOuter_left_right]

 theorem canonicalFixedNormSqCandidate_forces_left_right_right_left
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a : TriadicOuterBlock X .left .right)
    (b : TriadicOuterBlock X .right .left) :
    MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
      (CanonicalBlockTuple.compose_left_right_left X a b) =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) a *
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .left .right a)
    (CanonicalBlockTuple.embedOuter X .right .left b)
  calc
    MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
        (CanonicalBlockTuple.compose_left_right_left X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .left .right a)
            (CanonicalBlockTuple.embedOuter X .right .left b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_left_right_right_left X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_left_left X
            (CanonicalBlockTuple.compose_left_right_left X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .right a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .left b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_left_right,
            CanonicalBlockTuple.normSq_embedOuter_right_left]

 theorem canonicalFixedNormSqCandidate_forces_left_right_right_right
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a : TriadicOuterBlock X .left .right)
    (b : TriadicOuterBlock X .right .right) :
    MatrixNorm.Analytic.frobSqRect
      (ι := X.schur.brightBoundaryVertex)
      (κ := X.schur.darkBoundaryVertex)
      (CanonicalBlockTuple.compose_left_right_right X a b) =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .left .right a)
    (CanonicalBlockTuple.embedOuter X .right .right b)
  calc
    MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex)
        (CanonicalBlockTuple.compose_left_right_right X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .left .right a)
            (CanonicalBlockTuple.embedOuter X .right .right b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_left_right_right_right X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_left_right X
            (CanonicalBlockTuple.compose_left_right_right X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .right a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .right b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_left_right,
            CanonicalBlockTuple.normSq_embedOuter_right_right]

 theorem canonicalFixedNormSqCandidate_forces_center_center
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a b : TriadicCenterBlock X) :
    MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex)
      (CanonicalBlockTuple.compose_center X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedCenter X a)
    (CanonicalBlockTuple.embedCenter X b)
  calc
    MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex)
        (CanonicalBlockTuple.compose_center X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedCenter X a)
            (CanonicalBlockTuple.embedCenter X b)) := by
          rw [CanonicalBlockTuple.mul_embedCenter_center X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedCenter X
            (CanonicalBlockTuple.compose_center X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedCenter X a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedCenter X b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) a *
          MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedCenter,
            CanonicalBlockTuple.normSq_embedCenter]

 theorem canonicalFixedNormSqCandidate_forces_right_left_left_left
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a : TriadicOuterBlock X .right .left)
    (b : TriadicOuterBlock X .left .left) :
    MatrixNorm.Analytic.frobSqRect
      (ι := X.schur.darkBoundaryVertex)
      (κ := X.schur.brightBoundaryVertex)
      (CanonicalBlockTuple.compose_right_left_left X a b) =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .right .left a)
    (CanonicalBlockTuple.embedOuter X .left .left b)
  calc
    MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex)
        (CanonicalBlockTuple.compose_right_left_left X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .right .left a)
            (CanonicalBlockTuple.embedOuter X .left .left b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_right_left_left_left X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_right_left X
            (CanonicalBlockTuple.compose_right_left_left X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .left a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .left b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_right_left,
            CanonicalBlockTuple.normSq_embedOuter_left_left]

 theorem canonicalFixedNormSqCandidate_forces_right_left_left_right
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a : TriadicOuterBlock X .right .left)
    (b : TriadicOuterBlock X .left .right) :
    MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
      (CanonicalBlockTuple.compose_right_left_right X a b) =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) a *
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .right .left a)
    (CanonicalBlockTuple.embedOuter X .left .right b)
  calc
    MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
        (CanonicalBlockTuple.compose_right_left_right X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .right .left a)
            (CanonicalBlockTuple.embedOuter X .left .right b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_right_left_left_right X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_right_right X
            (CanonicalBlockTuple.compose_right_left_right X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .left a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .left .right b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_right_left,
            CanonicalBlockTuple.normSq_embedOuter_left_right]

 theorem canonicalFixedNormSqCandidate_forces_right_right_right_left
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a : TriadicOuterBlock X .right .right)
    (b : TriadicOuterBlock X .right .left) :
    MatrixNorm.Analytic.frobSqRect
      (ι := X.schur.darkBoundaryVertex)
      (κ := X.schur.brightBoundaryVertex)
      (CanonicalBlockTuple.compose_right_right_left X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .right .right a)
    (CanonicalBlockTuple.embedOuter X .right .left b)
  calc
    MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex)
        (CanonicalBlockTuple.compose_right_right_left X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .right .right a)
            (CanonicalBlockTuple.embedOuter X .right .left b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_right_right_right_left X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_right_left X
            (CanonicalBlockTuple.compose_right_right_left X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .right a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .left b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_right_right,
            CanonicalBlockTuple.normSq_embedOuter_right_left]

 theorem canonicalFixedNormSqCandidate_forces_right_right_right_right
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X)
    (a b : TriadicOuterBlock X .right .right) :
    MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
      (CanonicalBlockTuple.compose_right_right_right X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b := by
  have hmul := h.normSqMultiplicativeOnCanonicalProduct
    (CanonicalBlockTuple.embedOuter X .right .right a)
    (CanonicalBlockTuple.embedOuter X .right .right b)
  calc
    MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
        (CanonicalBlockTuple.compose_right_right_right X a b)
      = CanonicalBlockTuple.normSq X
          (CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X .right .right a)
            (CanonicalBlockTuple.embedOuter X .right .right b)) := by
          rw [CanonicalBlockTuple.mul_embedOuter_right_right_right_right X a b]
          symm
          exact CanonicalBlockTuple.normSq_embedOuter_right_right X
            (CanonicalBlockTuple.compose_right_right_right X a b)
    _ = CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .right a) *
          CanonicalBlockTuple.normSq X (CanonicalBlockTuple.embedOuter X .right .right b) := by
          exact hmul
    _ = MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
          MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b := by
          rw [CanonicalBlockTuple.normSq_embedOuter_right_right,
            CanonicalBlockTuple.normSq_embedOuter_right_right]

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
