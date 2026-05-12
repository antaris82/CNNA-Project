import CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary

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
Canonical single-carrier candidate for Slot 1: one tuple carrying all outer Schur blocks
plus the center block on a single product type.
This is the honest common surface shared by Slot 1 and Slot 2 before choosing
multiplication and norm.
-/
structure CanonicalBlockTuple (X : CayleyDicksonSource Cell T) where
  leftLeft : TriadicOuterBlock X .left .left
  leftRight : TriadicOuterBlock X .left .right
  center : TriadicCenterBlock X
  rightLeft : TriadicOuterBlock X .right .left
  rightRight : TriadicOuterBlock X .right .right

namespace CanonicalBlockTuple

variable (X : CayleyDicksonSource Cell T)

@[ext] theorem ext
    {a b : CanonicalBlockTuple X}
    (h_leftLeft : a.leftLeft = b.leftLeft)
    (h_leftRight : a.leftRight = b.leftRight)
    (h_center : a.center = b.center)
    (h_rightLeft : a.rightLeft = b.rightLeft)
    (h_rightRight : a.rightRight = b.rightRight) :
    a = b := by
  cases a
  cases b
  cases h_leftLeft
  cases h_leftRight
  cases h_center
  cases h_rightLeft
  cases h_rightRight
  rfl

instance : Zero (CanonicalBlockTuple X) where
  zero := {
    leftLeft := 0
    leftRight := 0
    center := 0
    rightLeft := 0
    rightRight := 0
  }

/-- Canonical embedding of an outer block into the common product carrier. -/
def embedOuter (κ η : ReducedRoleIndex) :
    TriadicOuterBlock X κ η → CanonicalBlockTuple X := by
  cases κ <;> cases η
  · intro a
    exact {
      leftLeft := a
      leftRight := 0
      center := 0
      rightLeft := 0
      rightRight := 0
    }
  · intro a
    exact {
      leftLeft := 0
      leftRight := a
      center := 0
      rightLeft := 0
      rightRight := 0
    }
  · intro a
    exact {
      leftLeft := 0
      leftRight := 0
      center := 0
      rightLeft := a
      rightRight := 0
    }
  · intro a
    exact {
      leftLeft := 0
      leftRight := 0
      center := 0
      rightLeft := 0
      rightRight := a
    }

/-- Canonical embedding of the center/interface block into the common carrier. -/
def embedCenter : TriadicCenterBlock X → CanonicalBlockTuple X := fun c => {
  leftLeft := 0
  leftRight := 0
  center := c
  rightLeft := 0
  rightRight := 0
}

@[simp] theorem embedOuter_left_left_leftLeft
    (a : TriadicOuterBlock X .left .left) :
    (embedOuter X .left .left a).leftLeft = a := by
  rfl

@[simp] theorem embedOuter_left_right_leftRight
    (a : TriadicOuterBlock X .left .right) :
    (embedOuter X .left .right a).leftRight = a := by
  rfl

@[simp] theorem embedOuter_right_left_rightLeft
    (a : TriadicOuterBlock X .right .left) :
    (embedOuter X .right .left a).rightLeft = a := by
  rfl

@[simp] theorem embedOuter_right_right_rightRight
    (a : TriadicOuterBlock X .right .right) :
    (embedOuter X .right .right a).rightRight = a := by
  rfl

@[simp] theorem embedCenter_center
    (c : TriadicCenterBlock X) :
    (embedCenter X c).center = c := by
  rfl

@[simp] theorem embedOuter_left_left_other
    (a : TriadicOuterBlock X .left .left) :
    (embedOuter X .left .left a).leftRight = 0 ∧
    (embedOuter X .left .left a).center = 0 ∧
    (embedOuter X .left .left a).rightLeft = 0 ∧
    (embedOuter X .left .left a).rightRight = 0 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

@[simp] theorem embedCenter_other
    (c : TriadicCenterBlock X) :
    (embedCenter X c).leftLeft = 0 ∧
    (embedCenter X c).leftRight = 0 ∧
    (embedCenter X c).rightLeft = 0 ∧
    (embedCenter X c).rightRight = 0 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/--
The common carrier already exists canonically; the remaining Slot-1 work is to equip
it with a canonical multiplication and prove the full alternative law.
-/
def carrierExists : Nonempty (CanonicalBlockTuple X) := by
  exact ⟨0⟩

end CanonicalBlockTuple

/--
Slot-1 carrier precursor: the common product carrier and its canonical embeddings are
already available before the multiplication law is fixed.
-/
structure Slot1CarrierCandidate (X : CayleyDicksonSource Cell T) where
  carrier : Type u
  embedOuter : ∀ κ η : ReducedRoleIndex, TriadicOuterBlock X κ η → carrier
  embedCenter : TriadicCenterBlock X → carrier

/-- Canonical Slot-1 carrier candidate coming directly from the Schur/triadic blocks. -/
def slot1CarrierCandidateOf (X : CayleyDicksonSource Cell T) :
    Slot1CarrierCandidate X where
  carrier := CanonicalBlockTuple X
  embedOuter := CanonicalBlockTuple.embedOuter X
  embedCenter := CanonicalBlockTuple.embedCenter X

/--
Current precise remaining Slot-1 gap after fixing the common carrier:
one still has to define a canonical multiplication on this carrier and prove full
alternativity on it.
-/
structure Slot1ProductLawRemaining (X : CayleyDicksonSource Cell T) where
  surface : AlternativeLawProductSurface X
  carrier_eq : surface.Carrier = (slot1CarrierCandidateOf X).carrier
  embedOuterCompatibility : Prop
  embedCenterCompatibility : Prop
  fullAlternativeLaw : FullAlternativeLaw surface

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
