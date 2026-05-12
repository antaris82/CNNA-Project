import CNNA.PillarA.Geometry.LCPMeasure

set_option autoImplicit false

namespace CNNA.PillarA.Geometry

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

section Foliation

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [AddressPresentation Cell Addr]

abbrev BundledAddress
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr] :=
  Σ n : Nat, Addr n

def foliationTime (x : BundledAddress (Cell := Cell) (Addr := Addr)) : Nat :=
  x.1

def foliationLayer (n : Nat) : Set (BundledAddress (Cell := Cell) (Addr := Addr)) :=
  {x | x.1 = n}

def bundledPrefix
    (x y : BundledAddress (Cell := Cell) (Addr := Addr)) : Prop :=
  AddressPresentation.PrefixRel Cell Addr x.2 y.2

instance instDecidableBundledPrefix
    (x y : BundledAddress (Cell := Cell) (Addr := Addr)) :
    Decidable (bundledPrefix (Cell := Cell) (Addr := Addr) x y) := by
  change Decidable (AddressPresentation.PrefixRel Cell Addr x.2 y.2)
  infer_instance

theorem mem_foliationLayer_iff
    (x : BundledAddress (Cell := Cell) (Addr := Addr)) (n : Nat) :
    x ∈ foliationLayer (Cell := Cell) (Addr := Addr) n ↔ x.1 = n := by
  rfl

theorem foliationTime_eq_of_mem_layer
    (x : BundledAddress (Cell := Cell) (Addr := Addr)) {n : Nat}
    (hx : x ∈ foliationLayer (Cell := Cell) (Addr := Addr) n) :
    foliationTime (Cell := Cell) (Addr := Addr) x = n := by
  exact (mem_foliationLayer_iff (Cell := Cell) (Addr := Addr) x n).mp hx

theorem prefix_level_mono {L M : Nat} {a : Addr L} {b : Addr M}
    (h : AddressPresentation.PrefixRel Cell Addr a b) :
    L ≤ M := by
  rcases h with ⟨hLM, _⟩
  exact hLM

theorem bundledPrefix_time_mono
    {x y : BundledAddress (Cell := Cell) (Addr := Addr)}
    (h : bundledPrefix (Cell := Cell) (Addr := Addr) x y) :
    foliationTime (Cell := Cell) (Addr := Addr) x ≤
      foliationTime (Cell := Cell) (Addr := Addr) y := by
  exact prefix_level_mono (Cell := Cell) (Addr := Addr) h

theorem eq_of_prefix_same_level {n : Nat} {a b : Addr n}
    (h : AddressPresentation.PrefixRel Cell Addr a b) :
    a = b := by
  rcases h with ⟨h', hh⟩
  have hk : h' = Nat.le_refl n := Subsingleton.elim _ _
  calc
    a = AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) h' b := hh.symm
    _ = b := by
      simpa [hk] using AddressPresentation.ancestor_refl (Cell := Cell) (Addr := Addr) b

theorem eq_of_mem_same_layer_and_prefix
    {x y : BundledAddress (Cell := Cell) (Addr := Addr)} {n : Nat}
    (hx : x ∈ foliationLayer (Cell := Cell) (Addr := Addr) n)
    (hy : y ∈ foliationLayer (Cell := Cell) (Addr := Addr) n)
    (hxy : bundledPrefix (Cell := Cell) (Addr := Addr) x y) :
    x = y := by
  cases x with
  | mk kx ax =>
      cases y with
      | mk ky ay =>
          have hkx : kx = n :=
            (mem_foliationLayer_iff (Cell := Cell) (Addr := Addr) ⟨kx, ax⟩ n).mp hx
          have hky : ky = n :=
            (mem_foliationLayer_iff (Cell := Cell) (Addr := Addr) ⟨ky, ay⟩ n).mp hy
          cases hkx
          cases hky
          have hEq : ax = ay :=
            eq_of_prefix_same_level (Cell := Cell) (Addr := Addr) hxy
          cases hEq
          rfl

end Foliation

end CNNA.PillarA.Geometry
