import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import CNNA.PillarA.Foundation.Determinism

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

namespace ConcreteSubstrate

/-- A concrete computable reference carrier: cells on level `L` are words of length `L`
    over an alphabet of size `b + 1`. The branching factor is therefore uniformly `b + 1`. -/
abbrev RegularCell (b : Nat) (L : Nat) : Type :=
  Fin L → Fin (b + 1)

instance instDecidableEqRegularCell (b : Nat) (L : Nat) : DecidableEq (RegularCell b L) := by
  infer_instance

instance instFintypeRegularCell (b : Nat) (L : Nat) : Fintype (RegularCell b L) := by
  infer_instance

def root (b : Nat) : RegularCell b 0 :=
  fun i => Fin.elim0 i

def parent {b L : Nat} (c : RegularCell b (L + 1)) : RegularCell b L :=
  fun i => c i.castSucc

def extend {b L : Nat} (p : RegularCell b L) (a : Fin (b + 1)) : RegularCell b (L + 1) :=
  fun i =>
    if h : i.1 < L then
      p ⟨i.1, h⟩
    else
      a

def children {b L : Nat} (p : RegularCell b L) : Finset (RegularCell b (L + 1)) :=
  Finset.univ.image (extend p)

theorem root_eq (b : Nat) (c : RegularCell b 0) : c = root b := by
  funext i
  exact Fin.elim0 i

theorem parent_extend {b L : Nat} (p : RegularCell b L) (a : Fin (b + 1)) :
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
      rw [hidx]

theorem extend_eq_of_parent_eq {b L : Nat}
    {p : RegularCell b L} {c : RegularCell b (L + 1)}
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
        rw [hidx]
  · have hge : L ≤ i.1 := Nat.le_of_not_lt h
    have hle : i.1 ≤ L := Nat.le_of_lt_succ i.2
    have hval : i.1 = L := Nat.le_antisymm hle hge
    have hi : i = Fin.last L := by
      apply Fin.ext
      exact hval
    calc
      extend p (c (Fin.last L)) i = c (Fin.last L) := by
        simp [extend, h]
      _ = c i := by
        rw [hi]

theorem mem_children_iff {b L : Nat}
    {p : RegularCell b L} {c : RegularCell b (L + 1)} :
    c ∈ children p ↔ parent c = p := by
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨a, -, hac⟩
    subst hac
    exact parent_extend p a
  · intro hpar
    refine Finset.mem_image.mpr ?_
    exact ⟨c (Fin.last L), Finset.mem_univ _, extend_eq_of_parent_eq hpar⟩

theorem children_nonempty {b L : Nat} (p : RegularCell b L) :
    (children p).Nonempty := by
  refine ⟨extend p 0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem extend_injective {b L : Nat} (p : RegularCell b L) :
    Function.Injective (extend p) := by
  intro a₁ a₂ h
  have hlast : extend p a₁ (Fin.last L) = extend p a₂ (Fin.last L) :=
    congrFun h (Fin.last L)
  simp [extend] at hlast
  exact hlast

theorem card_children {b L : Nat} (p : RegularCell b L) :
    (children p).card = b + 1 := by
  unfold children
  rw [Finset.card_image_of_injective _ (extend_injective (p := p))]
  simp

instance instSubstrateClassRegularCell (b : Nat) :
    SubstrateClass (RegularCell b) where
  instDecEq := by
    intro L
    infer_instance
  instFintype := by
    intro L
    infer_instance
  root := root b
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
    exact root_eq b c
  branching := fun {L} _ => b + 1
  branching_eq_card_children := by
    intro L c
    exact (card_children c).symm

instance instDeterministicSubstrateClassRegularCell (b : Nat) :
    DeterministicSubstrateClass (RegularCell b) where
  parent := parent
  parents_eq_singleton_parent := by
    intro L c
    rfl

def zeroCell (b L : Nat) : RegularCell b L :=
  fun _ => 0

def zeroThread (b : Nat) : InfiniteThread (Cell := RegularCell b) where
  cell := fun L => zeroCell b L
  coh := by
    intro L
    show parent (zeroCell b (L + 1)) ∈ ({parent (zeroCell b (L + 1))} : Finset (RegularCell b L))
    simp

theorem zeroThread_cell_zero (b : Nat) (L : Nat) (i : Fin L) :
    (zeroThread b).cell L i = 0 := by
  rfl

theorem zeroThread_root_eq (b : Nat) :
    (zeroThread b).cell 0 = SubstrateClass.root (Cell := RegularCell b) := by
  exact SubstrateClass.root_eq ((zeroThread b).cell 0)

abbrev ReferenceCellOf := RegularCell

end ConcreteSubstrate

end CNNA.PillarA.Foundation
