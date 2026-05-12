import CNNA.PillarA.Finite.CutSpec

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

structure RegionCore (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  support : CutSpec Cell T

abbrev RegionCoreOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  RegionCore (Cell := Cell) T

namespace RegionCore

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (R S : RegionCore Cell T)
    (hsupport : R.support = S.support) :
    R = S := by
  cases R with
  | mk supportR =>
    cases S with
    | mk supportS =>
      cases hsupport
      rfl

def cast (h : T = U) (R : RegionCore Cell T) : RegionCore Cell U := by
  cases h
  exact R

theorem cast_rfl (R : RegionCore Cell T) :
    cast (Cell := Cell) rfl R = R := by
  rfl

theorem support_cast (h : T = U) (R : RegionCore Cell T) :
    (RegionCore.cast (Cell := Cell) h R).support = CutSpec.cast (Cell := Cell) h R.support := by
  cases h
  rfl

def carrier (R : RegionCore Cell T) (L : Nat) : Finset (Cell L) :=
  R.support.carrier L

theorem carrier_subset (R : RegionCore Cell T) (L : Nat) :
    R.carrier L ⊆ T.carrier L :=
  R.support.carrier_subset L

def slice (R : RegionCore Cell T) (L : Nat) : LayerSlice Cell :=
  R.support.slice L

theorem slice_level (R : RegionCore Cell T) (L : Nat) :
    (R.slice L).level = L := by
  rfl

theorem slice_carrier (R : RegionCore Cell T) (L : Nat) :
    (R.slice L).carrier = R.carrier L := by
  rfl

def ofCutSpec (S : CutSpec Cell T) : RegionCore Cell T where
  support := S

theorem ofCutSpec_support (S : CutSpec Cell T) :
    (ofCutSpec S).support = S := rfl

theorem ofCutSpec_carrier (S : CutSpec Cell T) (L : Nat) :
    (ofCutSpec S).carrier L = S.carrier L := rfl

def parentExposedAt (R : RegionCore Cell T) : ∀ L : Nat, Cell L → Prop
  | 0, _ => False
  | L + 1, x =>
      ∃ p : Cell L,
        p ∈ SubstrateClass.parents x ∧
          p ∈ T.carrier L ∧
          p ∉ R.carrier L

def childExposedAt (R : RegionCore Cell T) : ∀ L : Nat, Cell L → Prop
  | L, x =>
      T.cutoff ≤ L ∨
        ∃ c : Cell (L + 1),
          c ∈ SubstrateClass.children x ∧
            c ∈ T.carrier (L + 1) ∧
            c ∉ R.carrier (L + 1)

instance decidableParentExposedAt (R : RegionCore Cell T) (L : Nat) (x : Cell L) :
    Decidable (R.parentExposedAt L x) := by
  cases L with
  | zero => exact isFalse id
  | succ L =>
    show Decidable (∃ p : Cell L,
      p ∈ SubstrateClass.parents x ∧ p ∈ T.carrier L ∧ p ∉ R.carrier L)
    exact Fintype.decidableExistsFintype

instance decidableChildExposedAt (R : RegionCore Cell T) (L : Nat) (x : Cell L) :
    Decidable (R.childExposedAt L x) := by
  show Decidable (T.cutoff ≤ L ∨
    ∃ c : Cell (L + 1),
      c ∈ SubstrateClass.children x ∧ c ∈ T.carrier (L + 1) ∧ c ∉ R.carrier (L + 1))
  exact instDecidableOr

theorem not_parentExposed_root (R : RegionCore Cell T) (x : Cell 0) :
    ¬ R.parentExposedAt 0 x := by
  intro hx
  exact hx

def boundaryCarrier (R : RegionCore Cell T) (L : Nat) : Finset (Cell L) :=
  (R.carrier L).filter (fun x => R.parentExposedAt L x ∨ R.childExposedAt L x)

abbrev BoundaryCarrierOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (R : RegionCore Cell T) (L : Nat) :=
  R.boundaryCarrier L

theorem boundaryCarrier_subset (R : RegionCore Cell T) (L : Nat) :
    R.boundaryCarrier L ⊆ R.carrier L := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem mem_boundaryCarrier_iff (R : RegionCore Cell T) {L : Nat} {x : Cell L} :
    x ∈ R.boundaryCarrier L ↔
      x ∈ R.carrier L ∧ (R.parentExposedAt L x ∨ R.childExposedAt L x) := by
  simp [RegionCore.boundaryCarrier]

def interiorCarrier (R : RegionCore Cell T) (L : Nat) : Finset (Cell L) :=
  (R.carrier L).filter (fun x => ¬ (R.parentExposedAt L x ∨ R.childExposedAt L x))

abbrev InteriorCarrierOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (R : RegionCore Cell T) (L : Nat) :=
  R.interiorCarrier L

theorem interiorCarrier_subset (R : RegionCore Cell T) (L : Nat) :
    R.interiorCarrier L ⊆ R.carrier L := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem mem_interiorCarrier_iff (R : RegionCore Cell T) {L : Nat} {x : Cell L} :
    x ∈ R.interiorCarrier L ↔
      x ∈ R.carrier L ∧ ¬ (R.parentExposedAt L x ∨ R.childExposedAt L x) := by
  simp [RegionCore.interiorCarrier]

theorem disjoint_interior_boundary (R : RegionCore Cell T) (L : Nat) :
    Disjoint (R.interiorCarrier L) (R.boundaryCarrier L) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxI hxB
  have hxI' := (R.mem_interiorCarrier_iff).mp hxI
  have hxB' := (R.mem_boundaryCarrier_iff).mp hxB
  exact hxI'.2 hxB'.2

theorem carrier_union_boundary_interior (R : RegionCore Cell T) (L : Nat) :
    R.interiorCarrier L ∪ R.boundaryCarrier L = R.carrier L := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxI | hxB
    · exact R.interiorCarrier_subset L hxI
    · exact R.boundaryCarrier_subset L hxB
  · intro hx
    by_cases hexp : R.parentExposedAt L x ∨ R.childExposedAt L x
    · exact Finset.mem_union.mpr <| Or.inr <| (R.mem_boundaryCarrier_iff).2 ⟨hx, hexp⟩
    · exact Finset.mem_union.mpr <| Or.inl <| (R.mem_interiorCarrier_iff).2 ⟨hx, hexp⟩

def interiorSlice (R : RegionCore Cell T) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := R.interiorCarrier L }

abbrev InteriorSliceOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (R : RegionCore Cell T) (L : Nat) :=
  R.interiorSlice L

theorem interiorSlice_level (R : RegionCore Cell T) (L : Nat) :
    (R.interiorSlice L).level = L := by
  rfl

theorem interiorSlice_carrier (R : RegionCore Cell T) (L : Nat) :
    (InteriorSliceOf Cell R L).carrier = InteriorCarrierOf Cell R L := by
  rfl

def boundarySlice (R : RegionCore Cell T) (L : Nat) : BoundarySlice Cell :=
  { level := L
    carrier := R.carrier L
    boundary := R.boundaryCarrier L
    boundary_subset := R.boundaryCarrier_subset L }

abbrev BoundarySliceOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (R : RegionCore Cell T) (L : Nat) :=
  R.boundarySlice L

theorem boundarySlice_level (R : RegionCore Cell T) (L : Nat) :
    (R.boundarySlice L).level = L := by
  rfl

theorem boundarySlice_carrier (R : RegionCore Cell T) (L : Nat) :
    (BoundarySliceOf Cell R L).carrier = R.carrier L := by
  rfl

theorem boundarySlice_boundary (R : RegionCore Cell T) (L : Nat) :
    (BoundarySliceOf Cell R L).boundary = BoundaryCarrierOf Cell R L := by
  rfl

end RegionCore

section Transport

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]

abbrev AddressRegionCore
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]
    (T : AddressTruncatedFamily Cell Addr) :=
  @RegionCore Addr
    (AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr))
    T

namespace RegionCore

def encode {T : TruncatedFamily Cell} (R : RegionCore Cell T) :
    AddressRegionCore Cell Addr
      (TruncatedFamily.encode (Cell := Cell) (Addr := Addr) T) := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  exact
    { support := CutSpec.encode (Cell := Cell) (Addr := Addr) R.support }

def decode
    {T : AddressTruncatedFamily Cell Addr}
    (R : AddressRegionCore Cell Addr T) :
    RegionCore Cell (TruncatedFamily.decode (Cell := Cell) (Addr := Addr) T) := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  exact
    { support := CutSpec.decode (Cell := Cell) (Addr := Addr) R.support }

theorem decode_encode {T : TruncatedFamily Cell} (R : RegionCore Cell T) :
    RegionCore.cast (Cell := Cell)
      (TruncatedFamily.decode_encode (Cell := Cell) (Addr := Addr) T)
      (RegionCore.decode (Cell := Cell) (Addr := Addr)
        (RegionCore.encode (Cell := Cell) (Addr := Addr) R)) = R := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine RegionCore.ext _ _ ?_
  rw [RegionCore.support_cast]
  simpa [RegionCore.encode, RegionCore.decode] using
    (CutSpec.decode_encode (Cell := Cell) (Addr := Addr) R.support)

theorem encode_decode
    {T : AddressTruncatedFamily Cell Addr}
    (R : AddressRegionCore Cell Addr T) :
    @RegionCore.cast Addr
      (AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr))
      (TruncatedFamily.encode (Cell := Cell) (Addr := Addr)
        (TruncatedFamily.decode (Cell := Cell) (Addr := Addr) T))
      T
      (TruncatedFamily.encode_decode (Cell := Cell) (Addr := Addr) T)
      (RegionCore.encode (Cell := Cell) (Addr := Addr)
        (RegionCore.decode (Cell := Cell) (Addr := Addr) R)) = R := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine RegionCore.ext _ _ ?_
  rw [RegionCore.support_cast]
  simpa [RegionCore.encode, RegionCore.decode] using
    (CutSpec.encode_decode (Cell := Cell) (Addr := Addr) R.support)

end RegionCore

end Transport

namespace ToCStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def regionCoreOfCut (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (S : FiniteCutOf Cell (X.approximant p)) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec S

def fullRegionVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec (CutSpec.full (X.approximant p))

def trunkRegionVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) (N : Nat) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec (CutSpec.TrunkCutOf Cell (X.approximant p) N)

def windowRegionVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) (lo hi : Nat) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec (CutSpec.WindowCutOf Cell (X.approximant p) lo hi)

def frontierRegionVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ (X.approximant p).carrier L) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec
    (CutSpec.AdaptiveFrontierCutOf Cell (X.approximant p) frontier hfrontier)

section Addressed

variable {Addr : Nat → Type v} [IdealAddressEquiv Cell Addr]

def cylinderRegionVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec
    (CylinderCutOf Cell Addr (X.approximant p) a N)

def subtreeRegionVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    RegionCoreOf Cell (X.approximant p) :=
  RegionCore.ofCutSpec
    (SubtreeCutOf Cell Addr (X.approximant p) a N)

end Addressed

end ToCStrong


namespace StrengtheningS4

def referenceFullRegion (b : Nat) (p : ConcretePolicyOf) :
    RegionCoreOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.fullRegionVariant (referenceToC b) p

def referenceCylinderRegion (b : Nat) (p : ConcretePolicyOf)
    {L : Nat} (a : ReferenceIdealAddrOf b L) (N : Nat) :
    RegionCoreOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.cylinderRegionVariant
    (Cell := ReferenceIdealCellOf b)
    (Addr := ReferenceIdealAddrOf b)
    (referenceToC b) p a N

def variationFullRegion (β : Nat → Nat) (p : ConcretePolicyOf) :
    RegionCoreOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ToCStrong.fullRegionVariant (variationToC β) p

end StrengtheningS4

end CNNA.PillarA.Finite
