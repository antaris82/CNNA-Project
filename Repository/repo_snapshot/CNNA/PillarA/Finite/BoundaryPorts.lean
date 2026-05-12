import CNNA.PillarA.Finite.RegionCore

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

structure BoundaryPorts (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  region : RegionCore Cell T

abbrev BoundaryPortsOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  BoundaryPorts (Cell := Cell) T

namespace BoundaryPorts

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

@[ext] theorem ext (B C : BoundaryPorts Cell T)
    (hregion : B.region = C.region) :
    B = C := by
  cases B with
  | mk regionB =>
    cases C with
    | mk regionC =>
      cases hregion
      rfl

def ofRegion (R : RegionCore Cell T) : BoundaryPorts Cell T where
  region := R

theorem ofRegion_region (R : RegionCore Cell T) :
    (ofRegion R).region = R := rfl

def carrier (B : BoundaryPorts Cell T) (L : Nat) : Finset (Cell L) :=
  B.region.carrier L

theorem carrier_eq (B : BoundaryPorts Cell T) (L : Nat) :
    B.carrier L = B.region.carrier L := rfl

def ports (B : BoundaryPorts Cell T) (L : Nat) : Finset (Cell L) :=
  B.region.boundaryCarrier L

abbrev PortsOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (B : BoundaryPorts Cell T) (L : Nat) :=
  B.ports L

theorem ports_eq_boundaryCarrier (B : BoundaryPorts Cell T) (L : Nat) :
    PortsOf Cell B L = RegionCore.BoundaryCarrierOf Cell B.region L := by
  rfl

theorem mem_ports_iff (B : BoundaryPorts Cell T) {L : Nat} {x : Cell L} :
    x ∈ B.ports L ↔
      x ∈ B.carrier L ∧
        (B.region.parentExposedAt L x ∨ B.region.childExposedAt L x) := by
  exact B.region.mem_boundaryCarrier_iff

theorem ports_subset_carrier (B : BoundaryPorts Cell T) (L : Nat) :
    B.ports L ⊆ B.carrier L :=
  B.region.boundaryCarrier_subset L

def interiorCarrier (B : BoundaryPorts Cell T) (L : Nat) : Finset (Cell L) :=
  B.region.interiorCarrier L

abbrev InteriorCarrierOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (B : BoundaryPorts Cell T) (L : Nat) :=
  B.interiorCarrier L

theorem interiorCarrier_eq (B : BoundaryPorts Cell T) (L : Nat) :
    B.interiorCarrier L = RegionCore.InteriorCarrierOf Cell B.region L := rfl

theorem mem_interiorCarrier_iff (B : BoundaryPorts Cell T) {L : Nat} {x : Cell L} :
    x ∈ B.interiorCarrier L ↔
      x ∈ B.carrier L ∧ ¬ (B.region.parentExposedAt L x ∨ B.region.childExposedAt L x) := by
  exact B.region.mem_interiorCarrier_iff

theorem interiorCarrier_subset_carrier (B : BoundaryPorts Cell T) (L : Nat) :
    B.interiorCarrier L ⊆ B.carrier L :=
  B.region.interiorCarrier_subset L

theorem interior_boundary_disjoint (B : BoundaryPorts Cell T) (L : Nat) :
    Disjoint (B.interiorCarrier L) (PortsOf Cell B L) := by
  exact B.region.disjoint_interior_boundary L

theorem carrier_union_interior_ports (B : BoundaryPorts Cell T) (L : Nat) :
    B.interiorCarrier L ∪ PortsOf Cell B L = B.carrier L := by
  exact B.region.carrier_union_boundary_interior L

def slice (B : BoundaryPorts Cell T) (L : Nat) : BoundarySlice Cell :=
  B.region.boundarySlice L

theorem slice_eq_boundarySlice (B : BoundaryPorts Cell T) (L : Nat) :
    B.slice L = RegionCore.BoundarySliceOf Cell B.region L := by
  rfl

theorem slice_level (B : BoundaryPorts Cell T) (L : Nat) :
    (B.slice L).level = L := by
  exact RegionCore.boundarySlice_level B.region L

theorem slice_carrier (B : BoundaryPorts Cell T) (L : Nat) :
    (B.slice L).carrier = B.carrier L := by
  exact RegionCore.boundarySlice_carrier B.region L

theorem slice_boundary (B : BoundaryPorts Cell T) (L : Nat) :
    (B.slice L).boundary = PortsOf Cell B L := by
  rw [B.ports_eq_boundaryCarrier L]
  exact RegionCore.boundarySlice_boundary B.region L

def portCount (B : BoundaryPorts Cell T) (L : Nat) : Nat :=
  (B.ports L).card

abbrev PortCountOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (B : BoundaryPorts Cell T) (L : Nat) :=
  B.portCount L

theorem portCount_eq_boundaryCard (B : BoundaryPorts Cell T) (L : Nat) :
    PortCountOf Cell B L = (B.slice L).boundaryCard := by
  rw [BoundaryPorts.PortCountOf]
  rw [BoundaryPorts.portCount]
  rw [BoundarySlice.boundaryCard]
  rw [B.slice_boundary]

end BoundaryPorts

namespace ToCStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def boundaryPortsOfCut (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (S : FiniteCutOf Cell (X.approximant p)) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (RegionCore.ofCutSpec S)

def fullBoundaryPortsVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (ToCStrong.fullRegionVariant X p)

def trunkBoundaryPortsVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) (N : Nat) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (ToCStrong.trunkRegionVariant X p N)

def windowBoundaryPortsVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) (lo hi : Nat) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (ToCStrong.windowRegionVariant X p lo hi)

def frontierBoundaryPortsVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ (X.approximant p).carrier L) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (ToCStrong.frontierRegionVariant X p frontier hfrontier)

section Addressed

variable {Addr : Nat → Type v} [IdealAddressEquiv Cell Addr]

def cylinderBoundaryPortsVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (ToCStrong.cylinderRegionVariant (Cell := Cell) (Addr := Addr) X p a N)

def subtreeBoundaryPortsVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    BoundaryPortsOf Cell (X.approximant p) :=
  BoundaryPorts.ofRegion (ToCStrong.subtreeRegionVariant (Cell := Cell) (Addr := Addr) X p a N)

end Addressed

end ToCStrong


namespace StrengtheningS4

def referenceFullBoundaryPorts (b : Nat) (p : ConcretePolicyOf) :
    BoundaryPortsOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.fullBoundaryPortsVariant (referenceToC b) p

def referenceCylinderBoundaryPorts (b : Nat) (p : ConcretePolicyOf)
    {L : Nat} (a : ReferenceIdealAddrOf b L) (N : Nat) :
    BoundaryPortsOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.cylinderBoundaryPortsVariant
    (Cell := ReferenceIdealCellOf b)
    (Addr := ReferenceIdealAddrOf b)
    (referenceToC b) p a N

def variationFullBoundaryPorts (β : Nat → Nat) (p : ConcretePolicyOf) :
    BoundaryPortsOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ToCStrong.fullBoundaryPortsVariant (variationToC β) p

end StrengtheningS4

end CNNA.PillarA.Finite
