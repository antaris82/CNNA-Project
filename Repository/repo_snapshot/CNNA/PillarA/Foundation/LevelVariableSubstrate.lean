import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import CNNA.PillarA.Foundation.Determinism

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

namespace LevelVariableSubstrate

abbrev LevelVariableCell (branching : Nat → Nat) (L : Nat) : Type :=
  (i : Fin L) → Fin (branching i.1 + 1)

local notation "VarCell[" β "," L "]" => LevelVariableCell β L

instance instDecidableEqLevelVariableCell (branching : Nat → Nat) (L : Nat) :
    DecidableEq VarCell[branching, L] := by
  infer_instance

instance instFintypeLevelVariableCell (branching : Nat → Nat) (L : Nat) :
    Fintype VarCell[branching, L] := by
  infer_instance

def root (branching : Nat → Nat) : VarCell[branching, 0] :=
  fun i => Fin.elim0 i

def parent {branching : Nat → Nat} {L : Nat} (c : VarCell[branching, L + 1]) :
    VarCell[branching, L] :=
  fun i => c i.castSucc

def extend {branching : Nat → Nat} {L : Nat}
    (p : VarCell[branching, L]) (a : Fin (branching L + 1)) :
    VarCell[branching, L + 1] :=
  fun i =>
    if h : i.1 < L then
      p ⟨i.1, h⟩
    else
      by
        have hge : L ≤ i.1 := Nat.le_of_not_lt h
        have hle : i.1 ≤ L := Nat.le_of_lt_succ i.2
        have hval : i.1 = L := Nat.le_antisymm hle hge
        exact hval.symm ▸ a

def children {branching : Nat → Nat} {L : Nat} (p : VarCell[branching, L]) :
    Finset VarCell[branching, L + 1] :=
  Finset.univ.image (extend p)

theorem root_eq (branching : Nat → Nat) (c : VarCell[branching, 0]) : c = root branching := by
  funext i
  exact Fin.elim0 i

theorem parent_extend {branching : Nat → Nat} {L : Nat}
    (p : VarCell[branching, L]) (a : Fin (branching L + 1)) :
    parent (extend p a) = p := by
  funext i
  have hi : (i.castSucc : Fin (L + 1)).1 < L := by
    exact i.2
  have hidx : (⟨(i.castSucc : Fin (L + 1)).1, hi⟩ : Fin L) = i := by
    apply Fin.ext
    rfl
  calc
    parent (extend p a) i = extend p a i.castSucc := by
      rfl
    _ = p ⟨(i.castSucc : Fin (L + 1)).1, hi⟩ := by
      simp [extend]
    _ = p i := by
      cases hidx
      rfl

theorem extend_eq_of_parent_eq {branching : Nat → Nat} {L : Nat}
    {p : VarCell[branching, L]} {c : VarCell[branching, L + 1]}
    (hpar : parent c = p) :
    extend p (c (Fin.last L)) = c := by
  funext i
  by_cases h : i.1 < L
  · have hidx : (⟨i.1, h⟩ : Fin L).castSucc = i := by
      apply Fin.ext
      rfl
    calc
      extend p (c (Fin.last L)) i = p ⟨i.1, h⟩ := by
        simp [extend, h]
      _ = parent c ⟨i.1, h⟩ := by
        exact (congrFun hpar ⟨i.1, h⟩).symm
      _ = c ((⟨i.1, h⟩ : Fin L).castSucc) := by
        rfl
      _ = c i := by
        cases hidx
        rfl
  · have hge : L ≤ i.1 := Nat.le_of_not_lt h
    have hle : i.1 ≤ L := Nat.le_of_lt_succ i.2
    have hval : i.1 = L := Nat.le_antisymm hle hge
    have hi : i = Fin.last L := by
      apply Fin.ext
      exact hval
    subst hi
    simp [extend]

theorem mem_children_iff {branching : Nat → Nat} {L : Nat}
    {p : VarCell[branching, L]} {c : VarCell[branching, L + 1]} :
    c ∈ children p ↔ parent c = p := by
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨a, -, hac⟩
    subst hac
    exact parent_extend p a
  · intro hpar
    refine Finset.mem_image.mpr ?_
    exact ⟨c (Fin.last L), Finset.mem_univ _, extend_eq_of_parent_eq hpar⟩

theorem children_nonempty {branching : Nat → Nat} {L : Nat} (p : VarCell[branching, L]) :
    (children p).Nonempty := by
  refine ⟨extend p 0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem extend_injective {branching : Nat → Nat} {L : Nat} (p : VarCell[branching, L]) :
    Function.Injective (extend p) := by
  intro a₁ a₂ h
  have hlast : extend p a₁ (Fin.last L) = extend p a₂ (Fin.last L) :=
    congrFun h (Fin.last L)
  simp [extend] at hlast
  exact hlast

theorem card_children {branching : Nat → Nat} {L : Nat} (p : VarCell[branching, L]) :
    (children p).card = branching L + 1 := by
  unfold children
  rw [Finset.card_image_of_injective _ (extend_injective (p := p))]
  simp

instance instSubstrateClassLevelVariableCell (branching : Nat → Nat) :
    SubstrateClass (LevelVariableCell branching) where
  instDecEq := by
    intro L
    infer_instance
  instFintype := by
    intro L
    infer_instance
  root := root branching
  parents := fun {L} c => {parent c}
  children := fun {L} p => children p
  parent_child_iff := by
    intro L p c
    constructor
    · intro hp
      have hp' : p = parent c := by
        simp at hp
        exact hp
      have hpar : parent c = p := hp'.symm
      exact (mem_children_iff (p := p) (c := c)).2 hpar
    · intro hc
      have hpar : parent c = p :=
        (mem_children_iff (p := p) (c := c)).1 hc
      simp [hpar]
  parents_nonempty := by
    intro L c
    refine ⟨parent c, ?_⟩
    simp
  children_nonempty := by
    intro L p
    exact children_nonempty p
  root_eq := by
    intro c
    exact root_eq branching c
  branching := fun {L} _ => branching L + 1
  branching_eq_card_children := by
    intro L c
    exact (card_children c).symm

instance instDeterministicSubstrateClassLevelVariableCell (branching : Nat → Nat) :
    DeterministicSubstrateClass (LevelVariableCell branching) where
  parent := parent
  parents_eq_singleton_parent := by
    intro L c
    rfl

def zeroCell (branching : Nat → Nat) (L : Nat) : VarCell[branching, L] :=
  fun _ => 0

def zeroThread (branching : Nat → Nat) : InfiniteThread (Cell := LevelVariableCell branching) where
  cell := fun L => zeroCell branching L
  coh := by
    intro L
    show parent (zeroCell branching (L + 1)) ∈ ({parent (zeroCell branching (L + 1))} : Finset VarCell[branching, L])
    simp

theorem zeroThread_cell_zero (branching : Nat → Nat) (L : Nat) (i : Fin L) :
    (zeroThread branching).cell L i = 0 := by
  rfl

theorem zeroThread_root_eq (branching : Nat → Nat) :
    (zeroThread branching).cell 0 =
      SubstrateClass.root (Cell := LevelVariableCell branching) := by
  exact SubstrateClass.root_eq ((zeroThread branching).cell 0)

theorem branching_eq_of_level {branching : Nat → Nat} {L : Nat}
    (c : VarCell[branching, L]) :
    SubstrateClass.branching c = branching L + 1 := by
  rfl

abbrev VariationCellOf := LevelVariableCell

end LevelVariableSubstrate

end CNNA.PillarA.Foundation
