import Mathlib

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u

class SubstrateClass (Cell : Nat → Type u) : Type (u + 1) where
  instDecEq : ∀ L : Nat, DecidableEq (Cell L)
  instFintype : ∀ L : Nat, Fintype (Cell L)
  root : Cell 0
  parents : ∀ {L : Nat}, Cell (L + 1) → Finset (Cell L)
  children : ∀ {L : Nat}, Cell L → Finset (Cell (L + 1))
  parent_child_iff :
    ∀ {L : Nat} (p : Cell L) (c : Cell (L + 1)),
      p ∈ parents c ↔ c ∈ children p
  parents_nonempty : ∀ {L : Nat} (c : Cell (L + 1)), (parents c).Nonempty
  children_nonempty : ∀ {L : Nat} (c : Cell L), (children c).Nonempty
  root_eq : ∀ c : Cell 0, c = root
  branching : ∀ {L : Nat}, Cell L → Nat
  branching_eq_card_children :
    ∀ {L : Nat} (c : Cell L), branching c = (children c).card

attribute [instance] SubstrateClass.instDecEq
attribute [instance] SubstrateClass.instFintype

namespace SubstrateClass

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def ParentRel {L : Nat} (c : Cell (L + 1)) (p : Cell L) : Prop :=
  p ∈ SubstrateClass.parents c

def ChildRel {L : Nat} (p : Cell L) (c : Cell (L + 1)) : Prop :=
  c ∈ SubstrateClass.children p

def refineSet {L : Nat} (S : Finset (Cell L)) : Finset (Cell (L + 1)) :=
  S.biUnion (fun c => SubstrateClass.children c)

def coarsenSet {L : Nat} (S : Finset (Cell (L + 1))) : Finset (Cell L) :=
  S.biUnion (fun c => SubstrateClass.parents c)

def rootLayer : Finset (Cell 0) :=
  {SubstrateClass.root (Cell := Cell)}

local notation "Σ₀[" Cell "]" => rootLayer (Cell := Cell)

theorem root_mem_rootLayer :
    SubstrateClass.root (Cell := Cell) ∈ Σ₀[Cell] := by
  simp [rootLayer]

theorem mem_rootLayer_iff (c : Cell 0) :
    c ∈ Σ₀[Cell] ↔ c = SubstrateClass.root (Cell := Cell) := by
  constructor
  · intro hc
    simpa [rootLayer] using hc
  · intro hc
    simp [rootLayer, hc]

theorem level_zero_subsingleton (c : Cell 0) :
    c = SubstrateClass.root (Cell := Cell) :=
  SubstrateClass.root_eq c

theorem parent_child {L : Nat} (p : Cell L) (c : Cell (L + 1)) :
    ParentRel (Cell := Cell) c p ↔ ChildRel (Cell := Cell) p c :=
  SubstrateClass.parent_child_iff p c

theorem parent_mem_of_child_mem {L : Nat} {p : Cell L} {c : Cell (L + 1)}
    (hc : c ∈ SubstrateClass.children p) :
    p ∈ SubstrateClass.parents c := by
  exact (SubstrateClass.parent_child_iff p c).mpr hc

theorem child_mem_of_parent_mem {L : Nat} {p : Cell L} {c : Cell (L + 1)}
    (hp : p ∈ SubstrateClass.parents c) :
    c ∈ SubstrateClass.children p := by
  exact (SubstrateClass.parent_child_iff p c).mp hp

theorem refineSet_mono {L : Nat} {S T : Finset (Cell L)} (h : S ⊆ T) :
    refineSet (Cell := Cell) S ⊆ refineSet (Cell := Cell) T := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨c, hcS, hxchild⟩
  exact Finset.mem_biUnion.mpr ⟨c, h hcS, hxchild⟩

theorem coarsenSet_mono {L : Nat} {S T : Finset (Cell (L + 1))} (h : S ⊆ T) :
    coarsenSet (Cell := Cell) S ⊆ coarsenSet (Cell := Cell) T := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨c, hcS, hxpar⟩
  exact Finset.mem_biUnion.mpr ⟨c, h hcS, hxpar⟩

theorem parent_exists {L : Nat} (c : Cell (L + 1)) :
    ∃ p : Cell L, p ∈ SubstrateClass.parents c := by
  rcases SubstrateClass.parents_nonempty c with ⟨p, hp⟩
  exact ⟨p, hp⟩

theorem child_exists {L : Nat} (c : Cell L) :
    ∃ d : Cell (L + 1), d ∈ SubstrateClass.children c := by
  rcases SubstrateClass.children_nonempty c with ⟨d, hd⟩
  exact ⟨d, hd⟩

theorem root_nonempty : Nonempty (Cell 0) :=
  ⟨SubstrateClass.root (Cell := Cell)⟩

theorem children_card_pos {L : Nat} (c : Cell L) :
    0 < (SubstrateClass.children c).card := by
  rcases SubstrateClass.children_nonempty c with ⟨d, hd⟩
  exact Finset.card_pos.mpr ⟨d, hd⟩

theorem branching_pos {L : Nat} (c : Cell L) :
    0 < SubstrateClass.branching c := by
  rw [SubstrateClass.branching_eq_card_children c]
  exact children_card_pos (Cell := Cell) c

end SubstrateClass

structure InfiniteThread (Cell : Nat → Type u) [SubstrateClass Cell] : Type (u + 1) where
  cell : ∀ L : Nat, Cell L
  coh : ∀ L : Nat, cell L ∈ SubstrateClass.parents (cell (L + 1))

namespace InfiniteThread

variable {Cell : Nat → Type u} [SubstrateClass Cell]

@[ext] theorem ext (U V : InfiniteThread (Cell := Cell))
    (h : ∀ L : Nat, U.cell L = V.cell L) : U = V := by
  cases U with
  | mk cellU cohU =>
    cases V with
    | mk cellV cohV =>
      have hcell : cellU = cellV := by
        funext L
        exact h L
      subst hcell
      have hcoh : cohU = cohV := by
        funext L
        exact Subsingleton.elim (cohU L) (cohV L)
      subst hcoh
      rfl

theorem cell_zero_eq_root (U : InfiniteThread (Cell := Cell)) :
    U.cell 0 = SubstrateClass.root (Cell := Cell) :=
  SubstrateClass.root_eq (U.cell 0)

end InfiniteThread

class DeterministicSubstrateClass (Cell : Nat → Type u)
    [SubstrateClass Cell] : Type (u + 1) where
  parent : ∀ {L : Nat}, Cell (L + 1) → Cell L
  parents_eq_singleton_parent :
    ∀ {L : Nat} (c : Cell (L + 1)),
      SubstrateClass.parents c = {parent c}

namespace DeterministicSubstrateClass

variable {Cell : Nat → Type u} [SubstrateClass Cell] [DeterministicSubstrateClass Cell]

theorem parent_mem_parents {L : Nat} (c : Cell (L + 1)) :
    (DeterministicSubstrateClass.parent (Cell := Cell) c) ∈ SubstrateClass.parents c := by
  simp [DeterministicSubstrateClass.parents_eq_singleton_parent (Cell := Cell) c]

theorem parent_unique {L : Nat} (c : Cell (L + 1)) {p : Cell L}
    (hp : p ∈ SubstrateClass.parents c) :
    p = DeterministicSubstrateClass.parent (Cell := Cell) c := by
  have hparents := DeterministicSubstrateClass.parents_eq_singleton_parent (Cell := Cell) c
  rw [hparents] at hp
  simpa using hp

end DeterministicSubstrateClass

end CNNA.PillarA.Foundation
