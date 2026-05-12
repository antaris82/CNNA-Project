import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate

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

/-- Carrier-level involution on the bright-bright block. -/
def leftLeftStar
    (a : TriadicOuterBlock X .left .left) :
    TriadicOuterBlock X .left .left :=
  Matrix.transpose a

/-- Carrier-level involution on the bright-dark block. -/
def leftRightStar
    (a : TriadicOuterBlock X .left .right) :
    TriadicOuterBlock X .right .left :=
  Matrix.transpose a

/-- Carrier-level involution on the interface block. -/
def centerStar
    (c : TriadicCenterBlock X) :
    TriadicCenterBlock X :=
  Matrix.transpose c

/-- Carrier-level involution on the dark-bright block. -/
def rightLeftStar
    (a : TriadicOuterBlock X .right .left) :
    TriadicOuterBlock X .left .right :=
  Matrix.transpose a

/-- Carrier-level involution on the dark-dark block. -/
def rightRightStar
    (a : TriadicOuterBlock X .right .right) :
    TriadicOuterBlock X .right .right :=
  Matrix.transpose a

/-- Carrier-level involution on the canonical common Slot-1/Slot-2 carrier. -/
def star (a : CanonicalBlockTuple X) : CanonicalBlockTuple X where
  leftLeft := leftLeftStar X a.leftLeft
  leftRight := rightLeftStar X a.rightLeft
  center := centerStar X a.center
  rightLeft := leftRightStar X a.leftRight
  rightRight := rightRightStar X a.rightRight

@[simp] theorem leftLeftStar_apply
    (a : TriadicOuterBlock X .left .left)
    (i j : X.schur.brightBoundaryVertex) :
    leftLeftStar X a i j = a j i := by
  rfl

@[simp] theorem leftRightStar_apply
    (a : TriadicOuterBlock X .left .right)
    (i : X.schur.darkBoundaryVertex)
    (j : X.schur.brightBoundaryVertex) :
    leftRightStar X a i j = a j i := by
  rfl

@[simp] theorem centerStar_apply
    (c : TriadicCenterBlock X)
    (i j : X.schur.interfaceBoundaryVertex) :
    centerStar X c i j = c j i := by
  rfl

@[simp] theorem rightLeftStar_apply
    (a : TriadicOuterBlock X .right .left)
    (i : X.schur.brightBoundaryVertex)
    (j : X.schur.darkBoundaryVertex) :
    rightLeftStar X a i j = a j i := by
  rfl

@[simp] theorem rightRightStar_apply
    (a : TriadicOuterBlock X .right .right)
    (i j : X.schur.darkBoundaryVertex) :
    rightRightStar X a i j = a j i := by
  rfl

@[simp] theorem leftLeftStar_zero :
    leftLeftStar X (0 : TriadicOuterBlock X .left .left) = 0 := by
  rfl

@[simp] theorem leftRightStar_zero :
    leftRightStar X (0 : TriadicOuterBlock X .left .right) = 0 := by
  rfl

@[simp] theorem centerStar_zero :
    centerStar X (0 : TriadicCenterBlock X) = 0 := by
  rfl

@[simp] theorem rightLeftStar_zero :
    rightLeftStar X (0 : TriadicOuterBlock X .right .left) = 0 := by
  rfl

@[simp] theorem rightRightStar_zero :
    rightRightStar X (0 : TriadicOuterBlock X .right .right) = 0 := by
  rfl

@[simp] theorem star_zero :
    star X (0 : CanonicalBlockTuple X) = 0 := by
  ext <;> rfl

@[simp] theorem leftLeftStar_star
    (a : TriadicOuterBlock X .left .left) :
    leftLeftStar X (leftLeftStar X a) = a := by
  rfl

@[simp] theorem leftRightStar_star
    (a : TriadicOuterBlock X .left .right) :
    rightLeftStar X (leftRightStar X a) = a := by
  rfl

@[simp] theorem centerStar_star
    (c : TriadicCenterBlock X) :
    centerStar X (centerStar X c) = c := by
  rfl

@[simp] theorem rightLeftStar_star
    (a : TriadicOuterBlock X .right .left) :
    leftRightStar X (rightLeftStar X a) = a := by
  rfl

@[simp] theorem rightRightStar_star
    (a : TriadicOuterBlock X .right .right) :
    rightRightStar X (rightRightStar X a) = a := by
  rfl

@[simp] theorem star_star
    (a : CanonicalBlockTuple X) :
    star X (star X a) = a := by
  ext <;> rfl

end CanonicalBlockTuple

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
