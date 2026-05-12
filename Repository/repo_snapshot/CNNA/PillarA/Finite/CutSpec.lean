import CNNA.PillarA.ToC.Notation

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

structure CutSpec (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  carrier : ∀ L : Nat, Finset (Cell L)
  carrier_subset : ∀ L : Nat, carrier L ⊆ T.carrier L

abbrev FiniteCutOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CutSpec (Cell := Cell) T

namespace CutSpec

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

@[ext] theorem ext (S U : CutSpec Cell T)
    (hcarrier : ∀ L : Nat, S.carrier L = U.carrier L) :
    S = U := by
  cases S with
  | mk carrierS subsetS =>
    cases U with
    | mk carrierU subsetU =>
      have hcar : carrierS = carrierU := by
        funext L
        exact hcarrier L
      subst hcar
      have hsubset : subsetS = subsetU := by
        exact Subsingleton.elim _ _
      subst hsubset
      rfl

def slice (S : CutSpec Cell T) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := S.carrier L }

theorem slice_level (S : CutSpec Cell T) (L : Nat) :
    (S.slice L).level = L := by
  rfl

theorem slice_carrier (S : CutSpec Cell T) (L : Nat) :
    (S.slice L).carrier = S.carrier L := by
  rfl

def cast {T U : TruncatedFamily Cell} (h : T = U)
    (S : CutSpec Cell T) : CutSpec Cell U := by
  cases h
  exact S

theorem cast_rfl {T : TruncatedFamily Cell} (S : CutSpec Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

theorem carrier_cast {T U : TruncatedFamily Cell} (h : T = U)
    (S : CutSpec Cell T) (L : Nat) :
    (CutSpec.cast (Cell := Cell) h S).carrier L = S.carrier L := by
  cases h
  rfl

def full (T : TruncatedFamily Cell) : CutSpec Cell T where
  carrier := T.carrier
  carrier_subset := by
    intro L
    exact subset_rfl

theorem full_carrier (T : TruncatedFamily Cell) (L : Nat) :
    (full T).carrier L = T.carrier L := rfl

theorem mem_full_iff (T : TruncatedFamily Cell) {L : Nat} {x : Cell L} :
    x ∈ (full T).carrier L ↔ x ∈ T.carrier L := Iff.rfl

def empty (T : TruncatedFamily Cell) : CutSpec Cell T where
  carrier := fun _ => ∅
  carrier_subset := by
    intro L x hx
    simp at hx

theorem empty_carrier (T : TruncatedFamily Cell) (L : Nat) :
    (empty T).carrier L = ∅ := rfl

theorem not_mem_empty_carrier (T : TruncatedFamily Cell) {L : Nat} {x : Cell L} :
    x ∉ (empty T).carrier L := by
  simp [empty]

def trunk (T : TruncatedFamily Cell) (N : Nat) : CutSpec Cell T := by
  refine
    { carrier := fun L => if L ≤ N then T.carrier L else ∅
      carrier_subset := ?_ }
  intro L x hx
  by_cases h : L ≤ N
  · simpa [h] using hx
  · simp [h] at hx

theorem trunk_carrier_le (T : TruncatedFamily Cell)
    {N L : Nat} (h : L ≤ N) :
    (trunk T N).carrier L = T.carrier L := by
  simp [trunk, h]

theorem trunk_carrier_gt (T : TruncatedFamily Cell)
    {N L : Nat} (h : N < L) :
    (trunk T N).carrier L = ∅ := by
  simp [trunk, Nat.not_le.mpr h]

def window (T : TruncatedFamily Cell) (lo hi : Nat) : CutSpec Cell T := by
  refine
    { carrier := fun L => if lo ≤ L ∧ L ≤ hi then T.carrier L else ∅
      carrier_subset := ?_ }
  intro L x hx
  by_cases h : lo ≤ L ∧ L ≤ hi
  · simpa [h] using hx
  · simp [h] at hx

theorem window_carrier_in (T : TruncatedFamily Cell)
    {lo hi L : Nat} (hlo : lo ≤ L) (hhi : L ≤ hi) :
    (window T lo hi).carrier L = T.carrier L := by
  simp [window, hlo, hhi]

theorem window_carrier_out (T : TruncatedFamily Cell)
    {lo hi L : Nat} (h : ¬(lo ≤ L ∧ L ≤ hi)) :
    (window T lo hi).carrier L = ∅ := by
  simp [window, h]

def adaptiveFrontier (T : TruncatedFamily Cell)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ T.carrier L) :
    CutSpec Cell T where
  carrier := frontier
  carrier_subset := hfrontier

theorem adaptiveFrontier_carrier (T : TruncatedFamily Cell)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ T.carrier L) (L : Nat) :
    (adaptiveFrontier T frontier hfrontier).carrier L = frontier L := rfl

abbrev TrunkCutOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) (N : Nat) :=
  CutSpec.trunk (Cell := Cell) T N

abbrev WindowCutOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) (lo hi : Nat) :=
  CutSpec.window (Cell := Cell) T lo hi

abbrev AdaptiveFrontierCutOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ T.carrier L) :=
  CutSpec.adaptiveFrontier (Cell := Cell) T frontier hfrontier

def exterior (S : CutSpec Cell T) : CutSpec Cell T where
  carrier := fun L => T.carrier L \ S.carrier L
  carrier_subset := by
    intro L x hx
    exact (Finset.mem_sdiff.mp hx).1

theorem mem_exterior_iff (S : CutSpec Cell T) {L : Nat} {x : Cell L} :
    x ∈ (S.exterior).carrier L ↔ x ∈ T.carrier L ∧ x ∉ S.carrier L := by
  simp [exterior]

theorem disjoint_carrier_exterior (S : CutSpec Cell T) (L : Nat) :
    Disjoint (S.carrier L) ((S.exterior).carrier L) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxS hxE
  have hx := (mem_exterior_iff (S := S)).mp hxE
  exact hx.2 hxS

theorem carrier_union_exterior (S : CutSpec Cell T) (L : Nat) :
    S.carrier L ∪ (S.exterior).carrier L = T.carrier L := by
  ext x
  by_cases hxS : x ∈ S.carrier L
  · have hxT : x ∈ T.carrier L := S.carrier_subset L hxS
    simp [exterior, hxS, hxT]
  · by_cases hxT : x ∈ T.carrier L
    · simp [exterior, hxS, hxT]
    · simp [exterior, hxS, hxT]

end CutSpec

section Transport

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]

abbrev AddressCutSpec
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]
    (T : AddressTruncatedFamily Cell Addr) :=
  @CutSpec Addr
    (AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr))
    T

namespace CutSpec

def encode {T : TruncatedFamily Cell} (S : CutSpec Cell T) :
    AddressCutSpec Cell Addr
      (TruncatedFamily.encode (Cell := Cell) (Addr := Addr) T) := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine
    { carrier := fun L => IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr) (S.carrier L)
      carrier_subset := ?_ }
  intro L a ha
  have hdec : IdealAddressEquiv.decode (Cell := Cell) (Addr := Addr) a ∈ S.carrier L := by
    exact (IdealAddressEquiv.mem_encodeSet (Cell := Cell) (Addr := Addr)).mp ha
  have hbase : IdealAddressEquiv.decode (Cell := Cell) (Addr := Addr) a ∈ T.carrier L :=
    S.carrier_subset L hdec
  change a ∈ IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr) (T.carrier L)
  exact (IdealAddressEquiv.mem_encodeSet (Cell := Cell) (Addr := Addr)).mpr hbase

def decode
    {T : AddressTruncatedFamily Cell Addr}
    (S : AddressCutSpec Cell Addr T) :
    CutSpec Cell (TruncatedFamily.decode (Cell := Cell) (Addr := Addr) T) := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine
    { carrier := fun L => IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr) (S.carrier L)
      carrier_subset := ?_ }
  intro L c hc
  have henc : IdealAddressEquiv.encode (Cell := Cell) (Addr := Addr) c ∈ S.carrier L := by
    exact (IdealAddressEquiv.mem_decodeSet (Cell := Cell) (Addr := Addr)).mp hc
  have hbase : IdealAddressEquiv.encode (Cell := Cell) (Addr := Addr) c ∈ T.carrier L :=
    S.carrier_subset L henc
  change c ∈ IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr) (T.carrier L)
  exact (IdealAddressEquiv.mem_decodeSet (Cell := Cell) (Addr := Addr)).mpr hbase

theorem decode_encode {T : TruncatedFamily Cell} (S : CutSpec Cell T) :
    CutSpec.cast (Cell := Cell)
      (TruncatedFamily.decode_encode (Cell := Cell) (Addr := Addr) T)
      (CutSpec.decode (Cell := Cell) (Addr := Addr)
        (CutSpec.encode (Cell := Cell) (Addr := Addr) S)) = S := by
  refine CutSpec.ext _ _ ?_
  intro L
  rw [CutSpec.carrier_cast]
  change IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr)
      (IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr) (S.carrier L)) = S.carrier L
  exact
    (IdealAddressEquiv.decodeSet_encodeSet (Cell := Cell) (Addr := Addr) (S := S.carrier L))

theorem encode_decode
    {T : AddressTruncatedFamily Cell Addr}
    (S : AddressCutSpec Cell Addr T) :
    @CutSpec.cast Addr
      (AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr))
      (TruncatedFamily.encode (Cell := Cell) (Addr := Addr)
        (TruncatedFamily.decode (Cell := Cell) (Addr := Addr) T))
      T
      (TruncatedFamily.encode_decode (Cell := Cell) (Addr := Addr) T)
      (CutSpec.encode (Cell := Cell) (Addr := Addr)
        (CutSpec.decode (Cell := Cell) (Addr := Addr) S)) = S := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine CutSpec.ext _ _ ?_
  intro L
  rw [CutSpec.carrier_cast]
  change IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr)
      (IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr) (S.carrier L)) = S.carrier L
  exact
    (IdealAddressEquiv.encodeSet_decodeSet (Cell := Cell) (Addr := Addr) (S := S.carrier L))

def addressCylinder
    {T : AddressTruncatedFamily Cell Addr}
    {L : Nat} (a : Addr L) (N : Nat) :
    AddressCutSpec Cell Addr T := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine
    { carrier := fun M =>
        if hLM : L ≤ M then
          if hMN : M ≤ N then
            (T.carrier M).filter (fun b => a ≼[Cell,Addr] b)
          else ∅
        else ∅
      carrier_subset := ?_ }
  intro M b hb
  by_cases hLM : L ≤ M
  · by_cases hMN : M ≤ N
    · have hb' : b ∈ (T.carrier M).filter (fun c => a ≼[Cell,Addr] c) := by
        simpa [hLM, hMN] using hb
      exact (Finset.mem_filter.mp hb').1
    · simp [hLM, hMN] at hb
  · simp [hLM] at hb

def cylinder
    {T : TruncatedFamily Cell}
    {L : Nat} (a : Addr L) (N : Nat) :
    CutSpec Cell T := by
  let Taddr : AddressTruncatedFamily Cell Addr :=
    TruncatedFamily.encode (Cell := Cell) (Addr := Addr) T
  exact
    CutSpec.cast (Cell := Cell)
      (TruncatedFamily.decode_encode (Cell := Cell) (Addr := Addr) T)
      (CutSpec.decode (Cell := Cell) (Addr := Addr)
        (T := Taddr)
        (CutSpec.addressCylinder (Cell := Cell) (Addr := Addr) (T := Taddr) a N))

def subtree
    {T : TruncatedFamily Cell}
    {L : Nat} (a : Addr L) (N : Nat) :
    CutSpec Cell T :=
  CutSpec.cylinder (Cell := Cell) (Addr := Addr) (T := T) a N

end CutSpec



end Transport

abbrev CylinderCutOf
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]
    (T : TruncatedFamily Cell) {L : Nat} (a : Addr L) (N : Nat) :=
  CutSpec.cylinder (Cell := Cell) (Addr := Addr) (T := T) a N

abbrev SubtreeCutOf
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]
    (T : TruncatedFamily Cell) {L : Nat} (a : Addr L) (N : Nat) :=
  CutSpec.subtree (Cell := Cell) (Addr := Addr) (T := T) a N

namespace ToCStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def fullVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    FiniteCutOf Cell (X.approximant p) :=
  CutSpec.full (X.approximant p)

def trunkVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf) (N : Nat) :
    FiniteCutOf Cell (X.approximant p) :=
  CutSpec.TrunkCutOf Cell (X.approximant p) N

def windowVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) (lo hi : Nat) :
    FiniteCutOf Cell (X.approximant p) :=
  CutSpec.WindowCutOf Cell (X.approximant p) lo hi

def frontierVariant (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (frontier : ∀ L : Nat, Finset (Cell L))
    (hfrontier : ∀ L : Nat, frontier L ⊆ (X.approximant p).carrier L) :
    FiniteCutOf Cell (X.approximant p) :=
  CutSpec.AdaptiveFrontierCutOf Cell (X.approximant p) frontier hfrontier


section Addressed

variable {Addr : Nat → Type v} [IdealAddressEquiv Cell Addr]

def cylinderVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    FiniteCutOf Cell (X.approximant p) :=
  CylinderCutOf Cell Addr (X.approximant p) a N

def subtreeVariant (X : ToCStrongOf Cell)
    (p : ConcretePolicyOf) {L : Nat} (a : Addr L) (N : Nat) :
    FiniteCutOf Cell (X.approximant p) :=
  SubtreeCutOf Cell Addr (X.approximant p) a N

end Addressed

end ToCStrong


namespace StrengtheningS4

def referenceFullCut (b : Nat) (p : ConcretePolicyOf) :
    FiniteCutOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.fullVariant (referenceToC b) p

theorem referenceFullCut_ideal (b : Nat) :
    (referenceToC b).ideal = 𝓓ref∞[b] := by
  rfl

def referenceCylinderCut (b : Nat) (p : ConcretePolicyOf)
    {L : Nat} (a : ReferenceIdealAddrOf b L) (N : Nat) :
    FiniteCutOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ToCStrong.cylinderVariant
    (Cell := ReferenceIdealCellOf b)
    (Addr := ReferenceIdealAddrOf b)
    (referenceToC b) p a N

def variationFullCut (β : Nat → Nat) (p : ConcretePolicyOf) :
    FiniteCutOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ToCStrong.fullVariant (variationToC β) p

end StrengtheningS4

end CNNA.PillarA.Finite
