import CNNA.PillarA.ToC.Addressing
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace CNNA.PillarA.Geometry

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

section LCPMeasure

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [AddressPresentation Cell Addr]

def CommonPrefixAt {L M : Nat} (a : Addr L) (b : Addr M) (n : Nat) : Prop :=
  ∃ h : n ≤ Nat.min L M,
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr)
      (Nat.le_trans h (Nat.min_le_left L M)) a =
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr)
      (Nat.le_trans h (Nat.min_le_right L M)) b

instance instDecidableCommonPrefixAt {L M : Nat} (a : Addr L) (b : Addr M) (n : Nat) :
    Decidable (CommonPrefixAt (Cell := Cell) (Addr := Addr) a b n) := by
  by_cases h : n ≤ Nat.min L M
  · refine decidable_of_iff
      (AddressPresentation.ancestor (Cell := Cell) (Addr := Addr)
          (Nat.le_trans h (Nat.min_le_left L M)) a =
        AddressPresentation.ancestor (Cell := Cell) (Addr := Addr)
          (Nat.le_trans h (Nat.min_le_right L M)) b) ?_
    constructor
    · intro hh
      exact ⟨h, hh⟩
    · intro hh
      rcases hh with ⟨h', hh'⟩
      have hk : h' = h := Subsingleton.elim _ _
      simpa [hk] using hh'
  · exact isFalse (by
      intro hh
      rcases hh with ⟨h', _⟩
      exact h h')

 theorem commonPrefixAt_zero {L M : Nat} (a : Addr L) (b : Addr M) :
    CommonPrefixAt (Cell := Cell) (Addr := Addr) a b 0 := by
  refine ⟨Nat.zero_le _, ?_⟩
  simp [AddressPresentation.ancestor_root]

theorem commonPrefixAt_self {L : Nat} (a : Addr L) :
    CommonPrefixAt (Cell := Cell) (Addr := Addr) a a L := by
  refine ⟨by simp, ?_⟩
  simp [AddressPresentation.ancestor_refl]

def lcpDepth {L M : Nat} (a : Addr L) (b : Addr M) : Nat :=
  Nat.findGreatest (CommonPrefixAt (Cell := Cell) (Addr := Addr) a b) (Nat.min L M)

theorem lcpDepth_le_min {L M : Nat} (a : Addr L) (b : Addr M) :
    lcpDepth (Cell := Cell) (Addr := Addr) a b ≤ Nat.min L M := by
  simpa [lcpDepth] using
    (Nat.findGreatest_le
      (P := CommonPrefixAt (Cell := Cell) (Addr := Addr) a b)
      (n := Nat.min L M))

theorem lcpDepth_le_left {L M : Nat} (a : Addr L) (b : Addr M) :
    lcpDepth (Cell := Cell) (Addr := Addr) a b ≤ L := by
  exact Nat.le_trans (lcpDepth_le_min (Cell := Cell) (Addr := Addr) a b) (Nat.min_le_left L M)

theorem lcpDepth_le_right {L M : Nat} (a : Addr L) (b : Addr M) :
    lcpDepth (Cell := Cell) (Addr := Addr) a b ≤ M := by
  exact Nat.le_trans (lcpDepth_le_min (Cell := Cell) (Addr := Addr) a b) (Nat.min_le_right L M)

theorem commonPrefixAt_lcpDepth {L M : Nat} (a : Addr L) (b : Addr M) :
    CommonPrefixAt (Cell := Cell) (Addr := Addr) a b
      (lcpDepth (Cell := Cell) (Addr := Addr) a b) := by
  exact Nat.findGreatest_spec
    (m := 0)
    (P := CommonPrefixAt (Cell := Cell) (Addr := Addr) a b)
    (n := Nat.min L M)
    (Nat.zero_le _)
    (commonPrefixAt_zero (Cell := Cell) (Addr := Addr) a b)

theorem lcpDepth_self {L : Nat} (a : Addr L) :
    lcpDepth (Cell := Cell) (Addr := Addr) a a = L := by
  have hself : CommonPrefixAt (Cell := Cell) (Addr := Addr) a a (Nat.min L L) := by
    simpa using (commonPrefixAt_self (Cell := Cell) (Addr := Addr) a)
  simpa [lcpDepth] using
    (Nat.findGreatest_eq
      (P := CommonPrefixAt (Cell := Cell) (Addr := Addr) a a)
      (n := Nat.min L L)
      hself)

def lcpAddress {L M : Nat} (a : Addr L) (b : Addr M) :
    Addr (lcpDepth (Cell := Cell) (Addr := Addr) a b) :=
  AddressPresentation.ancestor (Cell := Cell) (Addr := Addr)
    (lcpDepth_le_left (Cell := Cell) (Addr := Addr) a b) a

def lcpCell {L M : Nat} (a : Addr L) (b : Addr M) :
    Cell (lcpDepth (Cell := Cell) (Addr := Addr) a b) :=
  AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
    (lcpAddress (Cell := Cell) (Addr := Addr) a b)

def branchDistance {L M : Nat} (a : Addr L) (b : Addr M) : Nat :=
  (L - lcpDepth (Cell := Cell) (Addr := Addr) a b) +
    (M - lcpDepth (Cell := Cell) (Addr := Addr) a b)

theorem lcpAddress_prefix_left {L M : Nat} (a : Addr L) (b : Addr M) :
    AddressPresentation.PrefixRel Cell Addr
      (lcpAddress (Cell := Cell) (Addr := Addr) a b) a := by
  refine ⟨lcpDepth_le_left (Cell := Cell) (Addr := Addr) a b, ?_⟩
  rfl

theorem lcpAddress_eq_rightAncestor {L M : Nat} (a : Addr L) (b : Addr M) :
    lcpAddress (Cell := Cell) (Addr := Addr) a b =
      AddressPresentation.ancestor (Cell := Cell) (Addr := Addr)
        (lcpDepth_le_right (Cell := Cell) (Addr := Addr) a b) b := by
  rcases commonPrefixAt_lcpDepth (Cell := Cell) (Addr := Addr) a b with ⟨h, hh⟩
  have hleft : Nat.le_trans h (Nat.min_le_left L M) =
      lcpDepth_le_left (Cell := Cell) (Addr := Addr) a b := Subsingleton.elim _ _
  have hright : Nat.le_trans h (Nat.min_le_right L M) =
      lcpDepth_le_right (Cell := Cell) (Addr := Addr) a b := Subsingleton.elim _ _
  simpa [lcpAddress, hleft, hright] using hh

theorem lcpAddress_prefix_right {L M : Nat} (a : Addr L) (b : Addr M) :
    AddressPresentation.PrefixRel Cell Addr
      (lcpAddress (Cell := Cell) (Addr := Addr) a b) b := by
  refine ⟨lcpDepth_le_right (Cell := Cell) (Addr := Addr) a b, ?_⟩
  exact (lcpAddress_eq_rightAncestor (Cell := Cell) (Addr := Addr) a b).symm

theorem branchDistance_self {L : Nat} (a : Addr L) :
    branchDistance (Cell := Cell) (Addr := Addr) a a = 0 := by
  rw [branchDistance, lcpDepth_self (Cell := Cell) (Addr := Addr) a]
  simp

end LCPMeasure

end CNNA.PillarA.Geometry
