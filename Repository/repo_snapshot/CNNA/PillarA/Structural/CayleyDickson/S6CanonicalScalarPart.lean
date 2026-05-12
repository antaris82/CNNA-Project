import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar
import CNNA.PillarA.Foundation.MatrixNorms

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

/-- Star-derived scalar part of the bright-bright block. -/
def leftLeftScalarPart
    (a : TriadicOuterBlock X .left .left) : ℝ :=
  ∑ i : X.schur.brightBoundaryVertex,
    ∑ j : X.schur.brightBoundaryVertex,
      a i j * (leftLeftStar X a) j i

/-- Star-derived scalar part of the bright-dark block. -/
def leftRightScalarPart
    (a : TriadicOuterBlock X .left .right) : ℝ :=
  ∑ i : X.schur.brightBoundaryVertex,
    ∑ j : X.schur.darkBoundaryVertex,
      a i j * (leftRightStar X a) j i

/-- Star-derived scalar part of the interface block. -/
def centerScalarPart
    (c : TriadicCenterBlock X) : ℝ :=
  ∑ i : X.schur.interfaceBoundaryVertex,
    ∑ j : X.schur.interfaceBoundaryVertex,
      c i j * (centerStar X c) j i

/-- Star-derived scalar part of the dark-bright block. -/
def rightLeftScalarPart
    (a : TriadicOuterBlock X .right .left) : ℝ :=
  ∑ i : X.schur.darkBoundaryVertex,
    ∑ j : X.schur.brightBoundaryVertex,
      a i j * (rightLeftStar X a) j i

/-- Star-derived scalar part of the dark-dark block. -/
def rightRightScalarPart
    (a : TriadicOuterBlock X .right .right) : ℝ :=
  ∑ i : X.schur.darkBoundaryVertex,
    ∑ j : X.schur.darkBoundaryVertex,
      a i j * (rightRightStar X a) j i

@[simp] theorem leftLeftScalarPart_eq_frobSq
    (a : TriadicOuterBlock X .left .left) :
    leftLeftScalarPart X a =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a := by
  unfold leftLeftScalarPart MatrixNorm.Analytic.frobSq
  simp [CanonicalBlockTuple.leftLeftStar_apply, pow_two]

@[simp] theorem leftRightScalarPart_eq_frobSqRect
    (a : TriadicOuterBlock X .left .right) :
    leftRightScalarPart X a =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.brightBoundaryVertex)
        (κ := X.schur.darkBoundaryVertex) a := by
  unfold leftRightScalarPart MatrixNorm.Analytic.frobSqRect
  simp [CanonicalBlockTuple.leftRightStar_apply, pow_two]

@[simp] theorem centerScalarPart_eq_frobSq
    (c : TriadicCenterBlock X) :
    centerScalarPart X c =
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) c := by
  unfold centerScalarPart MatrixNorm.Analytic.frobSq
  simp [CanonicalBlockTuple.centerStar_apply, pow_two]

@[simp] theorem rightLeftScalarPart_eq_frobSqRect
    (a : TriadicOuterBlock X .right .left) :
    rightLeftScalarPart X a =
      MatrixNorm.Analytic.frobSqRect
        (ι := X.schur.darkBoundaryVertex)
        (κ := X.schur.brightBoundaryVertex) a := by
  unfold rightLeftScalarPart MatrixNorm.Analytic.frobSqRect
  simp [CanonicalBlockTuple.rightLeftStar_apply, pow_two]

@[simp] theorem rightRightScalarPart_eq_frobSq
    (a : TriadicOuterBlock X .right .right) :
    rightRightScalarPart X a =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a := by
  unfold rightRightScalarPart MatrixNorm.Analytic.frobSq
  simp [CanonicalBlockTuple.rightRightStar_apply, pow_two]

@[simp] theorem leftLeftScalarPart_zero :
    leftLeftScalarPart X (0 : TriadicOuterBlock X .left .left) = 0 := by
  rw [leftLeftScalarPart_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq]

@[simp] theorem leftRightScalarPart_zero :
    leftRightScalarPart X (0 : TriadicOuterBlock X .left .right) = 0 := by
  rw [leftRightScalarPart_eq_frobSqRect]
  simp [MatrixNorm.Analytic.frobSqRect]

@[simp] theorem centerScalarPart_zero :
    centerScalarPart X (0 : TriadicCenterBlock X) = 0 := by
  rw [centerScalarPart_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq]

@[simp] theorem rightLeftScalarPart_zero :
    rightLeftScalarPart X (0 : TriadicOuterBlock X .right .left) = 0 := by
  rw [rightLeftScalarPart_eq_frobSqRect]
  simp [MatrixNorm.Analytic.frobSqRect]

@[simp] theorem rightRightScalarPart_zero :
    rightRightScalarPart X (0 : TriadicOuterBlock X .right .right) = 0 := by
  rw [rightRightScalarPart_eq_frobSq]
  simp [MatrixNorm.Analytic.frobSq]

end CanonicalBlockTuple

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
