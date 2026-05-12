import CNNA.PillarA.ToC.Contract
import CNNA.PillarA.Foundation.Notation

set_option autoImplicit false

namespace CNNA.PillarA.ToC

open CNNA.PillarA.Foundation

universe u v

class AddressPresentation
    (Cell : Nat → Type u) (Addr : Nat → Type v) [SubstrateClass Cell] : Type (max u v + 1) where
  instDecEq : ∀ L : Nat, DecidableEq (Addr L)
  instFintype : ∀ L : Nat, Fintype (Addr L)
  root : Addr 0
  parent : ∀ {L : Nat}, Addr (L + 1) → Addr L
  children : ∀ {L : Nat}, Addr L → Finset (Addr (L + 1))
  parent_eq_iff_mem_children :
    ∀ {L : Nat} (a : Addr L) (b : Addr (L + 1)),
      parent b = a ↔ b ∈ children a
  children_nonempty : ∀ {L : Nat} (a : Addr L), (children a).Nonempty
  root_eq : ∀ a : Addr 0, a = root
  ancestor : ∀ {L M : Nat}, M ≤ L → Addr L → Addr M
  ancestor_refl : ∀ {L : Nat} (a : Addr L), ancestor (Nat.le_refl L) a = a
  ancestor_step : ∀ {L : Nat} (a : Addr (L + 1)),
      ancestor (Nat.le_succ L) a = parent a
  ancestor_comp : ∀ {L M N : Nat} (hLM : L ≤ M) (hMN : M ≤ N) (a : Addr N),
      ancestor hLM (ancestor hMN a) = ancestor (Nat.le_trans hLM hMN) a
  ancestor_root : ∀ {L : Nat} (a : Addr L), ancestor (Nat.zero_le L) a = root
  cellOf : ∀ {L : Nat}, Addr L → Cell L
  addressOf : ∀ {L : Nat}, Cell L → Addr L
  cellOf_addressOf : ∀ {L : Nat} (c : Cell L), cellOf (addressOf c) = c
  addressOf_cellOf : ∀ {L : Nat} (a : Addr L), addressOf (cellOf a) = a
  parent_respects_cells : ∀ {L : Nat} (a : Addr (L + 1)),
      cellOf (parent a) ∈ SubstrateClass.parents (cellOf a)

attribute [instance] AddressPresentation.instDecEq
attribute [instance] AddressPresentation.instFintype

namespace AddressPresentation

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [AddressPresentation Cell Addr]

theorem parent_eq_iff_mem_children' {L : Nat} (a : Addr L) (b : Addr (L + 1)) :
    AddressPresentation.parent (Cell := Cell) (Addr := Addr) b = a ↔
      b ∈ AddressPresentation.children (Cell := Cell) (Addr := Addr) a := by
  exact AddressPresentation.parent_eq_iff_mem_children (Cell := Cell) (Addr := Addr) a b

theorem child_mem_of_parent_eq {L : Nat} {a : Addr L} {b : Addr (L + 1)}
    (h : AddressPresentation.parent (Cell := Cell) (Addr := Addr) b = a) :
    b ∈ AddressPresentation.children (Cell := Cell) (Addr := Addr) a := by
  exact (parent_eq_iff_mem_children' (Cell := Cell) (Addr := Addr) a b).mp h

theorem parent_eq_of_child_mem {L : Nat} {a : Addr L} {b : Addr (L + 1)}
    (h : b ∈ AddressPresentation.children (Cell := Cell) (Addr := Addr) a) :
    AddressPresentation.parent (Cell := Cell) (Addr := Addr) b = a := by
  exact (parent_eq_iff_mem_children' (Cell := Cell) (Addr := Addr) a b).mpr h

theorem addressOf_injective {L : Nat} :
    Function.Injective (AddressPresentation.addressOf (Cell := Cell) (Addr := Addr) (L := L)) := by
  intro c d h
  have h' := congrArg
    (fun a => AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) (L := L) a) h
  simpa [AddressPresentation.cellOf_addressOf (Cell := Cell) (Addr := Addr)] using h'

theorem cellOf_injective {L : Nat} :
    Function.Injective (AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) (L := L)) := by
  intro a b h
  have h' := congrArg
    (fun c => AddressPresentation.addressOf (Cell := Cell) (Addr := Addr) (L := L) c) h
  simpa [AddressPresentation.addressOf_cellOf (Cell := Cell) (Addr := Addr)] using h'

theorem address_eq_iff_cell_eq {L : Nat} {a b : Addr L} :
    a = b ↔
      AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) a =
        AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact cellOf_injective (Cell := Cell) (Addr := Addr) h

theorem addressOf_cellOf_eq {L : Nat} (a : Addr L) :
    AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
      (AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) a) = a := by
  exact AddressPresentation.addressOf_cellOf (Cell := Cell) (Addr := Addr) a

theorem cellOf_addressOf_eq {L : Nat} (c : Cell L) :
    AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
      (AddressPresentation.addressOf (Cell := Cell) (Addr := Addr) c) = c := by
  exact AddressPresentation.cellOf_addressOf (Cell := Cell) (Addr := Addr) c

theorem addressOf_root_eq_root :
    AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
      (SubstrateClass.root (Cell := Cell)) =
        AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
  exact AddressPresentation.root_eq (Cell := Cell) (Addr := Addr)
    (AddressPresentation.addressOf (Cell := Cell) (Addr := Addr) (SubstrateClass.root (Cell := Cell)))

theorem cellOf_root_eq_root :
    AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
      (AddressPresentation.root (Cell := Cell) (Addr := Addr)) =
        SubstrateClass.root (Cell := Cell) := by
  calc
    AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
        (AddressPresentation.root (Cell := Cell) (Addr := Addr))
      = AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
          (AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
            (SubstrateClass.root (Cell := Cell))) := by
            rw [addressOf_root_eq_root (Cell := Cell) (Addr := Addr)]
    _ = SubstrateClass.root (Cell := Cell) :=
      AddressPresentation.cellOf_addressOf (Cell := Cell) (Addr := Addr)
        (SubstrateClass.root (Cell := Cell))

theorem ancestor_one_eq_parent {L : Nat} (a : Addr (L + 1)) :
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) (Nat.le_succ L) a =
      AddressPresentation.parent (Cell := Cell) (Addr := Addr) a := by
  exact AddressPresentation.ancestor_step (Cell := Cell) (Addr := Addr) a

theorem ancestor_zero_eq_root {L : Nat} (a : Addr L) :
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) (Nat.zero_le L) a =
      AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
  exact AddressPresentation.ancestor_root (Cell := Cell) (Addr := Addr) a

theorem parent_cell_mem {L : Nat} (a : Addr (L + 1)) :
    AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
      (AddressPresentation.parent (Cell := Cell) (Addr := Addr) a) ∈
        SubstrateClass.parents
          (AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) a) := by
  exact AddressPresentation.parent_respects_cells (Cell := Cell) (Addr := Addr) a

theorem child_cell_mem_of_mem_children {L : Nat} {a : Addr L} {b : Addr (L + 1)}
    (h : b ∈ AddressPresentation.children (Cell := Cell) (Addr := Addr) a) :
    AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) b ∈
      SubstrateClass.children
        (AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) a) := by
  have hparent : AddressPresentation.parent (Cell := Cell) (Addr := Addr) b = a :=
    parent_eq_of_child_mem (Cell := Cell) (Addr := Addr) h
  have hp : AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
      (AddressPresentation.parent (Cell := Cell) (Addr := Addr) b) ∈
        SubstrateClass.parents
          (AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) b) :=
    parent_cell_mem (Cell := Cell) (Addr := Addr) b
  have hp' : AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) a ∈
      SubstrateClass.parents
        (AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) b) := by
    simpa [hparent] using hp
  exact SubstrateClass.child_mem_of_parent_mem (Cell := Cell) hp'

def addressSubstrate (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr] :
    SubstrateClass Addr where
  instDecEq := AddressPresentation.instDecEq (Cell := Cell) (Addr := Addr)
  instFintype := AddressPresentation.instFintype (Cell := Cell) (Addr := Addr)
  root := AddressPresentation.root (Cell := Cell) (Addr := Addr)
  parents := fun {L} a => {AddressPresentation.parent (Cell := Cell) (Addr := Addr) a}
  children := AddressPresentation.children (Cell := Cell) (Addr := Addr)
  parent_child_iff := by
    intro L p c
    constructor
    · intro hp
      have hp' : p = AddressPresentation.parent (Cell := Cell) (Addr := Addr) c :=
        Finset.mem_singleton.mp hp
      exact (AddressPresentation.parent_eq_iff_mem_children
        (Cell := Cell) (Addr := Addr) p c).mp hp'.symm
    · intro hc
      have hp : AddressPresentation.parent (Cell := Cell) (Addr := Addr) c = p :=
        (AddressPresentation.parent_eq_iff_mem_children
          (Cell := Cell) (Addr := Addr) p c).mpr hc
      rw [← hp]
      simp
  parents_nonempty := by
    intro L a
    exact ⟨AddressPresentation.parent (Cell := Cell) (Addr := Addr) a, by simp⟩
  children_nonempty := AddressPresentation.children_nonempty (Cell := Cell) (Addr := Addr)
  root_eq := AddressPresentation.root_eq (Cell := Cell) (Addr := Addr)
  branching := fun {L} a =>
    (AddressPresentation.children (Cell := Cell) (Addr := Addr) a).card
  branching_eq_card_children := by
    intro L a
    rfl

def equivAt (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr] (L : Nat) : Addr L ≃ Cell L where
  toFun := AddressPresentation.cellOf (Cell := Cell) (Addr := Addr)
  invFun := AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
  left_inv := AddressPresentation.addressOf_cellOf (Cell := Cell) (Addr := Addr)
  right_inv := AddressPresentation.cellOf_addressOf (Cell := Cell) (Addr := Addr)

abbrev AddressFamily
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr] :=
  @DirectedFamily Addr (addressSubstrate (Cell := Cell) (Addr := Addr))

abbrev AddressThread
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr] :=
  @IdealThread Addr (addressSubstrate (Cell := Cell) (Addr := Addr))

def Prefix
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) : Prop :=
  ∃ h : L ≤ M,
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) h b = a

abbrev PrefixRel
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) : Prop :=
  Prefix Cell Addr a b

local notation:50 a " ≼[" Cell "," Addr "] " b => PrefixRel Cell Addr a b

instance decidablePrefix {L M : Nat} (a : Addr L) (b : Addr M) :
    Decidable (Prefix Cell Addr a b) := by
  by_cases hLM : L ≤ M
  · refine decidable_of_iff
      (AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) hLM b = a) ?_
    constructor
    · intro h
      exact ⟨hLM, h⟩
    · intro h
      rcases h with ⟨h', hh'⟩
      have hh : h' = hLM := Subsingleton.elim _ _
      simpa [hh] using hh'
  · refine isFalse ?_
    intro h
    rcases h with ⟨h', _⟩
    exact hLM h'

@[refl] theorem prefix_refl {L : Nat} (a : Addr L) : a ≼[Cell,Addr] a := by
  refine ⟨Nat.le_refl L, ?_⟩
  exact AddressPresentation.ancestor_refl (Cell := Cell) (Addr := Addr) a

@[trans] theorem prefix_trans {L M N : Nat} {a : Addr L} {b : Addr M} {c : Addr N}
    (hab : a ≼[Cell,Addr] b)
    (hbc : b ≼[Cell,Addr] c) :
    a ≼[Cell,Addr] c := by
  rcases hab with ⟨hLM, habEq⟩
  rcases hbc with ⟨hMN, hbcEq⟩
  refine ⟨Nat.le_trans hLM hMN, ?_⟩
  calc
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) (Nat.le_trans hLM hMN) c
        = AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) hLM
            (AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) hMN c) := by
            symm
            exact AddressPresentation.ancestor_comp (Cell := Cell) (Addr := Addr) hLM hMN c
    _ = AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) hLM b := by
          rw [hbcEq]
    _ = a := habEq

theorem root_prefix {M : Nat} (b : Addr M) :
    AddressPresentation.root (Cell := Cell) (Addr := Addr) ≼[Cell,Addr] b := by
  refine ⟨Nat.zero_le M, ?_⟩
  exact AddressPresentation.ancestor_root (Cell := Cell) (Addr := Addr) b

theorem parent_prefix {L : Nat} (b : Addr (L + 1)) :
    AddressPresentation.parent (Cell := Cell) (Addr := Addr) b ≼[Cell,Addr] b := by
  refine ⟨Nat.le_succ L, ?_⟩
  exact ancestor_one_eq_parent (Cell := Cell) (Addr := Addr) b

theorem prefix_of_mem_children {L : Nat} {a : Addr L} {b : Addr (L + 1)}
    (h : b ∈ AddressPresentation.children (Cell := Cell) (Addr := Addr) a) :
    a ≼[Cell,Addr] b := by
  have hparent : AddressPresentation.parent (Cell := Cell) (Addr := Addr) b = a :=
    parent_eq_of_child_mem (Cell := Cell) (Addr := Addr) h
  refine ⟨Nat.le_succ L, ?_⟩
  calc
    AddressPresentation.ancestor (Cell := Cell) (Addr := Addr) (Nat.le_succ L) b
        = AddressPresentation.parent (Cell := Cell) (Addr := Addr) b :=
          ancestor_one_eq_parent (Cell := Cell) (Addr := Addr) b
    _ = a := hparent

end AddressPresentation

end CNNA.PillarA.ToC
