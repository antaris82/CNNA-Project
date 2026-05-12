import CNNA.PillarA.Finite.BoundaryPorts

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

structure ApproximantStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  box : BoundaryPorts Cell T

abbrev ApproximantStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ApproximantStrong (Cell := Cell) T

abbrev ApproximantOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ApproximantStrong (Cell := Cell) T

namespace ApproximantStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (A B : ApproximantStrong Cell T)
    (hbox : A.box = B.box) :
    A = B := by
  cases A with
  | mk boxA =>
    cases B with
    | mk boxB =>
      cases hbox
      rfl

def cast (h : T = U) (A : ApproximantStrong Cell T) :
    ApproximantStrong Cell U := by
  cases h
  exact A

theorem cast_rfl (A : ApproximantStrong Cell T) :
    cast (Cell := Cell) rfl A = A := by
  rfl

def ofBoundaryPorts (B : BoundaryPorts Cell T) : ApproximantStrong Cell T where
  box := B

theorem ofBoundaryPorts_box (B : BoundaryPorts Cell T) :
    (ofBoundaryPorts B).box = B := rfl

def support (A : ApproximantStrong Cell T) : CutSpec Cell T :=
  A.box.region.support

theorem support_eq (A : ApproximantStrong Cell T) :
    A.support = A.box.region.support := by
  rfl

def region (A : ApproximantStrong Cell T) : RegionCore Cell T :=
  A.box.region

theorem region_eq (A : ApproximantStrong Cell T) :
    A.region = A.box.region := by
  rfl

def carrier (A : ApproximantStrong Cell T) (L : Nat) : Finset (Cell L) :=
  A.box.carrier L

abbrev CarrierOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) (L : Nat) :=
  A.carrier L

theorem carrier_eq_box_carrier (A : ApproximantStrong Cell T) (L : Nat) :
    A.carrier L = A.box.carrier L := by
  rfl

theorem carrier_eq_support_carrier (A : ApproximantStrong Cell T) (L : Nat) :
    A.carrier L = A.support.carrier L := by
  rfl

theorem carrier_subset (A : ApproximantStrong Cell T) (L : Nat) :
    A.carrier L ⊆ T.carrier L := by
  intro x hx
  exact A.box.region.carrier_subset L hx

def ports (A : ApproximantStrong Cell T) (L : Nat) : Finset (Cell L) :=
  A.box.ports L

abbrev PortsOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) (L : Nat) :=
  A.ports L

theorem ports_eq_box_ports (A : ApproximantStrong Cell T) (L : Nat) :
    A.ports L = A.box.ports L := by
  rfl

theorem ports_subset_carrier (A : ApproximantStrong Cell T) (L : Nat) :
    A.ports L ⊆ A.carrier L :=
  A.box.ports_subset_carrier L

theorem mem_ports_iff (A : ApproximantStrong Cell T) {L : Nat} {x : Cell L} :
    x ∈ A.ports L ↔
      x ∈ A.carrier L ∧
        (A.region.parentExposedAt L x ∨ A.region.childExposedAt L x) := by
  exact A.box.mem_ports_iff

def interiorCarrier (A : ApproximantStrong Cell T) (L : Nat) : Finset (Cell L) :=
  A.box.interiorCarrier L

abbrev InteriorCarrierOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) (L : Nat) :=
  A.interiorCarrier L

theorem interiorCarrier_eq_box_interior (A : ApproximantStrong Cell T) (L : Nat) :
    A.interiorCarrier L = A.box.interiorCarrier L := by
  rfl

theorem interiorCarrier_subset_carrier (A : ApproximantStrong Cell T) (L : Nat) :
    A.interiorCarrier L ⊆ A.carrier L :=
  A.box.interiorCarrier_subset_carrier L

theorem mem_interiorCarrier_iff (A : ApproximantStrong Cell T) {L : Nat} {x : Cell L} :
    x ∈ A.interiorCarrier L ↔
      x ∈ A.carrier L ∧
        ¬ (A.region.parentExposedAt L x ∨ A.region.childExposedAt L x) := by
  exact A.box.mem_interiorCarrier_iff

theorem interior_boundary_disjoint (A : ApproximantStrong Cell T) (L : Nat) :
    Disjoint (A.interiorCarrier L) (A.ports L) :=
  A.box.interior_boundary_disjoint L

theorem carrier_union_interior_ports (A : ApproximantStrong Cell T) (L : Nat) :
    A.interiorCarrier L ∪ A.ports L = A.carrier L :=
  A.box.carrier_union_interior_ports L

def slice (A : ApproximantStrong Cell T) (L : Nat) : BoundarySlice Cell :=
  A.box.slice L

abbrev SliceOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) (L : Nat) :=
  A.slice L

theorem slice_eq_box_slice (A : ApproximantStrong Cell T) (L : Nat) :
    A.slice L = A.box.slice L := by
  rfl

theorem slice_level (A : ApproximantStrong Cell T) (L : Nat) :
    (A.slice L).level = L := by
  exact BoundaryPorts.slice_level A.box L

theorem slice_carrier (A : ApproximantStrong Cell T) (L : Nat) :
    (A.slice L).carrier = A.carrier L := by
  exact BoundaryPorts.slice_carrier A.box L

theorem slice_boundary (A : ApproximantStrong Cell T) (L : Nat) :
    (A.slice L).boundary = A.ports L := by
  exact BoundaryPorts.slice_boundary A.box L

def interiorSlice (A : ApproximantStrong Cell T) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := A.interiorCarrier L }

abbrev InteriorSliceOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) (L : Nat) :=
  A.interiorSlice L

theorem interiorSlice_level (A : ApproximantStrong Cell T) (L : Nat) :
    (A.interiorSlice L).level = L := by
  rfl

theorem interiorSlice_carrier (A : ApproximantStrong Cell T) (L : Nat) :
    (A.interiorSlice L).carrier = A.interiorCarrier L := by
  rfl

def cutoff (_ : ApproximantStrong Cell T) : Nat :=
  T.cutoff

theorem cutoff_eq_truncation (A : ApproximantStrong Cell T) :
    A.cutoff = T.cutoff := by
  rfl

def topCarrier (A : ApproximantStrong Cell T) : Finset (Cell T.cutoff) :=
  A.carrier T.cutoff

def topPorts (A : ApproximantStrong Cell T) : Finset (Cell T.cutoff) :=
  A.ports T.cutoff

def topInteriorCarrier (A : ApproximantStrong Cell T) : Finset (Cell T.cutoff) :=
  A.interiorCarrier T.cutoff

def topSlice (A : ApproximantStrong Cell T) : BoundarySlice Cell :=
  A.slice T.cutoff

theorem topSlice_level (A : ApproximantStrong Cell T) :
    A.topSlice.level = T.cutoff := by
  exact A.slice_level T.cutoff

theorem topSlice_carrier (A : ApproximantStrong Cell T) :
    A.topSlice.carrier = A.topCarrier := by
  rfl

theorem topSlice_boundary (A : ApproximantStrong Cell T) :
    A.topSlice.boundary = A.topPorts := by
  rfl

def topInteriorSlice (A : ApproximantStrong Cell T) : LayerSlice Cell :=
  A.interiorSlice T.cutoff

theorem topInteriorSlice_level (A : ApproximantStrong Cell T) :
    A.topInteriorSlice.level = T.cutoff := by
  rfl

theorem topInteriorSlice_carrier (A : ApproximantStrong Cell T) :
    A.topInteriorSlice.carrier = A.topInteriorCarrier := by
  rfl

def portCount (A : ApproximantStrong Cell T) (L : Nat) : Nat :=
  (A.ports L).card

theorem portCount_eq_boundaryCard (A : ApproximantStrong Cell T) (L : Nat) :
    A.portCount L = (A.slice L).boundaryCard := by
  rw [ApproximantStrong.portCount, BoundarySlice.boundaryCard, A.slice_boundary]

def topPortCount (A : ApproximantStrong Cell T) : Nat :=
  A.portCount T.cutoff

end ApproximantStrong

namespace ToCStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def approximantOfBoundaryPorts (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (B : BoundaryPortsOf Cell (X.approximant p)) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts B

def approximantOfCut (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (S : FiniteCutOf Cell (X.approximant p)) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts (ToCStrong.boundaryPortsOfCut X p S)

def fullApproximantVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts (ToCStrong.fullBoundaryPortsVariant X p)

def trunkApproximantVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) (N : Nat) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts (ToCStrong.trunkBoundaryPortsVariant X p N)

def windowApproximantVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) (lo hi : Nat) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts (ToCStrong.windowBoundaryPortsVariant X p lo hi)

def frontierApproximantVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ (X.approximant p).carrier L) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts
    (ToCStrong.frontierBoundaryPortsVariant X p frontier hfrontier)

section Addressed

variable {Addr : Nat → Type v} [IdealAddressEquiv Cell Addr]

def cylinderApproximantVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts
    (ToCStrong.cylinderBoundaryPortsVariant (Cell := Cell) (Addr := Addr) X p a N)

def subtreeApproximantVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    ApproximantStrongOf Cell (X.approximant p) :=
  ApproximantStrong.ofBoundaryPorts
    (ToCStrong.subtreeBoundaryPortsVariant (Cell := Cell) (Addr := Addr) X p a N)

end Addressed

end ToCStrong


namespace StrengtheningS4

def referenceFullApproximant (b : Nat) (p : ConcretePolicyOf) :
    ApproximantStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.fullApproximantVariant (referenceToC b) p

def referenceCylinderApproximant (b : Nat) (p : ConcretePolicyOf)
    {L : Nat} (a : ReferenceIdealAddrOf b L) (N : Nat) :
    ApproximantStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.cylinderApproximantVariant
    (Cell := ReferenceIdealCellOf b)
    (Addr := ReferenceIdealAddrOf b)
    (referenceToC b) p a N

def variationFullApproximant (β : Nat → Nat) (p : ConcretePolicyOf) :
    ApproximantStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ToCStrong.fullApproximantVariant (variationToC β) p

end StrengtheningS4

end CNNA.PillarA.Finite
