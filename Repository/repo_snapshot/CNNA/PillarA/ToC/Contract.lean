import CNNA.PillarA.Foundation.Determinism
import CNNA.PillarA.Foundation.Notation

set_option autoImplicit false

namespace CNNA.PillarA.ToC

open CNNA.PillarA.Foundation

universe u

section BasicSlices

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def singletonSlice {L : Nat} (c : Cell L) : LayerSlice Cell :=
  { level := L
    carrier := {c} }

theorem singletonSlice_level {L : Nat} (c : Cell L) :
    (singletonSlice (Cell := Cell) c).level = L := by
  rfl

theorem singletonSlice_carrier {L : Nat} (c : Cell L) :
    (singletonSlice (Cell := Cell) c).carrier = ({c} : Finset (Cell L)) := by
  rfl

theorem mem_singletonSlice_iff {L : Nat} (c x : Cell L) :
    x ∈ (singletonSlice (Cell := Cell) c).carrier ↔ x = c := by
  simp [singletonSlice]

theorem singleton_mem_singletonSlice {L : Nat} (c : Cell L) :
    c ∈ (singletonSlice (Cell := Cell) c).carrier := by
  simp [singletonSlice]

def rootSlice : LayerSlice Cell :=
  singletonSlice (Cell := Cell) (SubstrateClass.root (Cell := Cell))

theorem rootSlice_level :
    (rootSlice (Cell := Cell)).level = 0 := by
  rfl

theorem rootSlice_carrier :
    (rootSlice (Cell := Cell)).carrier = Σ₀[Cell] := by
  rfl

theorem root_mem_rootSlice :
    SubstrateClass.root (Cell := Cell) ∈ (rootSlice (Cell := Cell)).carrier := by
  simp [rootSlice, singletonSlice]

theorem mem_rootSlice_iff (c : Cell 0) :
    c ∈ (rootSlice (Cell := Cell)).carrier ↔ c = SubstrateClass.root (Cell := Cell) := by
  simp [rootSlice, singletonSlice]

theorem carrier_eq_rootSlice_of_level_zero_and_root_mem
    {carrier : Finset (Cell 0)}
    (hroot : SubstrateClass.root (Cell := Cell) ∈ carrier) :
    carrier = (rootSlice (Cell := Cell)).carrier := by
  ext x
  constructor
  · intro hx
    have hxroot : x = SubstrateClass.root (Cell := Cell) := SubstrateClass.root_eq x
    simp [rootSlice, singletonSlice, hxroot]
  · intro _
    have hxroot : x = SubstrateClass.root (Cell := Cell) := SubstrateClass.root_eq x
    simpa [rootSlice, singletonSlice, hxroot] using hroot

def emptyOrigin : LayerSlice Cell :=
  rootSlice (Cell := Cell)

theorem emptyOrigin_level :
    (emptyOrigin (Cell := Cell)).level = 0 := by
  rfl

theorem emptyOrigin_carrier :
    (emptyOrigin (Cell := Cell)).carrier = (rootSlice (Cell := Cell)).carrier := by
  rfl

theorem root_mem_emptyOrigin :
    SubstrateClass.root (Cell := Cell) ∈ (emptyOrigin (Cell := Cell)).carrier := by
  change SubstrateClass.root (Cell := Cell) ∈ Σ₀[Cell]
  exact SubstrateClass.root_mem_rootLayer (Cell := Cell)

def parentSlice {L : Nat} (c : Cell (L + 1)) : LayerSlice Cell :=
  { level := L
    carrier := SubstrateClass.parents c }

theorem parentSlice_level {L : Nat} (c : Cell (L + 1)) :
    (parentSlice (Cell := Cell) c).level = L := by
  rfl

theorem mem_parentSlice_iff {L : Nat} (c : Cell (L + 1)) (p : Cell L) :
    p ∈ (parentSlice (Cell := Cell) c).carrier ↔ p ∈ SubstrateClass.parents c := by
  rfl

theorem parentSlice_nonempty {L : Nat} (c : Cell (L + 1)) :
    ((parentSlice (Cell := Cell) c).carrier).Nonempty := by
  exact SubstrateClass.parents_nonempty c

def childSlice {L : Nat} (c : Cell L) : LayerSlice Cell :=
  { level := L + 1
    carrier := SubstrateClass.children c }

theorem childSlice_level {L : Nat} (c : Cell L) :
    (childSlice (Cell := Cell) c).level = L + 1 := by
  rfl

theorem mem_childSlice_iff {L : Nat} (c : Cell L) (d : Cell (L + 1)) :
    d ∈ (childSlice (Cell := Cell) c).carrier ↔ d ∈ SubstrateClass.children c := by
  rfl

theorem childSlice_nonempty {L : Nat} (c : Cell L) :
    ((childSlice (Cell := Cell) c).carrier).Nonempty := by
  exact SubstrateClass.children_nonempty c

def branchingAt {L : Nat} (c : Cell L) : Nat :=
  SubstrateClass.branching c

theorem branchingAt_eq_card_childSlice {L : Nat} (c : Cell L) :
    branchingAt (Cell := Cell) c = ((childSlice (Cell := Cell) c).carrier).card := by
  simpa [branchingAt, childSlice] using SubstrateClass.branching_eq_card_children c

theorem branchingAt_pos {L : Nat} (c : Cell L) :
    0 < branchingAt (Cell := Cell) c := by
  simpa [branchingAt] using SubstrateClass.branching_pos (Cell := Cell) c

theorem no_terminal_stage {L : Nat} (c : Cell L) :
    ((childSlice (Cell := Cell) c).carrier).Nonempty :=
  childSlice_nonempty (Cell := Cell) c

end BasicSlices

section DirectedFamilies

variable {Cell : Nat → Type u} [SubstrateClass Cell]

structure DirectedFamily where
  carrier : ∀ L : Nat, Finset (Cell L)
  rooted : carrier 0 = Σ₀[Cell]
  forward : ∀ L : Nat, carrier (L + 1) ⊆ RefineSetOf (Cell := Cell) (carrier L)

namespace DirectedFamily

def slice (F : DirectedFamily (Cell := Cell)) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := F.carrier L }

theorem slice_level (F : DirectedFamily (Cell := Cell)) (L : Nat) :
    (F.slice L).level = L := by
  rfl

theorem slice_carrier (F : DirectedFamily (Cell := Cell)) (L : Nat) :
    (F.slice L).carrier = F.carrier L := by
  rfl

theorem root_mem (F : DirectedFamily (Cell := Cell)) :
    SubstrateClass.root (Cell := Cell) ∈ F.carrier 0 := by
  rw [F.rooted]
  simpa using (root_mem_rootSlice (Cell := Cell))

theorem zero_slice_nonempty (F : DirectedFamily (Cell := Cell)) :
    (F.carrier 0).Nonempty := by
  exact ⟨SubstrateClass.root (Cell := Cell), root_mem (Cell := Cell) F⟩

theorem forward_mem (F : DirectedFamily (Cell := Cell)) {L : Nat}
    {x : Cell (L + 1)} (hx : x ∈ F.carrier (L + 1)) :
    x ∈ RefineSetOf (Cell := Cell) (F.carrier L) := by
  exact F.forward L hx

end DirectedFamily

abbrev IdealThread (Cell : Nat → Type u) [SubstrateClass Cell] :=
  InfiniteThread Cell

namespace IdealThread

variable (U : IdealThread Cell)

def carrier (L : Nat) : Finset (Cell L) :=
  {(U.cell L)}

def slice (L : Nat) : LayerSlice Cell :=
  singletonSlice (Cell := Cell) (U.cell L)

theorem slice_carrier (L : Nat) :
    (U.slice L).carrier = U.carrier L := by
  rfl

theorem slice_level (L : Nat) :
    (U.slice L).level = L := by
  rfl

theorem rooted_carrier :
    U.carrier 0 = Σ₀[Cell] := by
  ext x
  constructor
  · intro hx
    have hx' : x = U.cell 0 := by
      simpa [carrier] using hx
    rw [InfiniteThread.cell_zero_eq_root (U := U)] at hx'
    exact (SubstrateClass.mem_rootLayer_iff (Cell := Cell) x).2 hx'
  · intro hx
    have hx' : x = SubstrateClass.root (Cell := Cell) :=
      (SubstrateClass.mem_rootLayer_iff (Cell := Cell) x).1 hx
    have hx'' : x = U.cell 0 := by
      calc
        x = SubstrateClass.root (Cell := Cell) := hx'
        _ = U.cell 0 := (InfiniteThread.cell_zero_eq_root (U := U)).symm
    simpa [carrier] using hx''

theorem root_mem_carrier :
    SubstrateClass.root (Cell := Cell) ∈ U.carrier 0 := by
  rw [U.rooted_carrier]
  simpa using (SubstrateClass.root_mem_rootLayer (Cell := Cell))

def family : DirectedFamily (Cell := Cell) where
  carrier := U.carrier
  rooted := U.rooted_carrier
  forward := by
    intro L x hx
    have hx' : x = U.cell (L + 1) := by
      simpa [carrier] using hx
    subst hx'
    have hchild : U.cell (L + 1) ∈ SubstrateClass.children (U.cell L) :=
      SubstrateClass.child_mem_of_parent_mem (Cell := Cell) (hp := U.coh L)
    simpa [carrier, SubstrateClass.refineSet] using hchild

theorem family_slice_eq (L : Nat) :
    (U.family.slice L).carrier = U.carrier L := by
  rfl

theorem family_rooted :
    (U.family).carrier 0 = Σ₀[Cell] := by
  exact U.rooted_carrier

end IdealThread

section Deterministic

variable {Cell : Nat → Type u} [SubstrateClass Cell] [DeterministicSubstrateClass Cell]

namespace DirectedFamily

theorem coarsen_succ_subset (F : DirectedFamily (Cell := Cell)) (L : Nat) :
    SubstrateClass.coarsenSet (F.carrier (L + 1)) ⊆ F.carrier L := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨c, hc, hpParent⟩
  have hrefine : c ∈ SubstrateClass.refineSet (Cell := Cell) (F.carrier L) :=
    F.forward_mem hc
  rcases Finset.mem_biUnion.mp hrefine with ⟨p', hp', hcChild⟩
  have hpEq : p = DeterministicSubstrateClass.parent (Cell := Cell) c :=
    DeterministicSubstrateClass.parent_unique (Cell := Cell) (c := c) (p := p) (hp := hpParent)
  have hp'Parent : p' ∈ SubstrateClass.parents c :=
    SubstrateClass.parent_mem_of_child_mem (Cell := Cell) (hc := hcChild)
  have hp'Eq : p' = DeterministicSubstrateClass.parent (Cell := Cell) c :=
    DeterministicSubstrateClass.parent_unique (Cell := Cell) (c := c) (p := p') (hp := hp'Parent)
  have hpp' : p = p' := by
    exact hpEq.trans hp'Eq.symm
  exact hpp' ▸ hp'

end DirectedFamily

theorem coarsen_singleton_eq_parent {L : Nat} (c : Cell (L + 1)) :
    SubstrateClass.coarsenSet ({c} : Finset (Cell (L + 1))) =
      {DeterministicSubstrateClass.parent (Cell := Cell) c} := by
  ext p
  simp [SubstrateClass.coarsenSet,
    DeterministicSubstrateClass.parents_eq_singleton_parent (Cell := Cell) c]

namespace IdealThread

variable (U : IdealThread Cell)

theorem coarsen_carrier_eq_prev (L : Nat) :
    SubstrateClass.coarsenSet (U.carrier (L + 1)) = U.carrier L := by
  have hparent : DeterministicSubstrateClass.parent (Cell := Cell) (U.cell (L + 1)) = U.cell L := by
    exact (DeterministicSubstrateClass.parent_unique
      (Cell := Cell) (c := U.cell (L + 1)) (p := U.cell L) (hp := U.coh L)).symm
  calc
    SubstrateClass.coarsenSet (U.carrier (L + 1))
        = {DeterministicSubstrateClass.parent (Cell := Cell) (U.cell (L + 1))} := by
            simp [carrier, coarsen_singleton_eq_parent]
    _ = {U.cell L} := by simp [hparent]
    _ = U.carrier L := by simp [carrier]

theorem family_coarsen_eq_prev (L : Nat) :
    SubstrateClass.coarsenSet ((U.family).carrier (L + 1)) = (U.family).carrier L := by
  change SubstrateClass.coarsenSet (U.carrier (L + 1)) = U.carrier L
  exact U.coarsen_carrier_eq_prev L

end IdealThread

end Deterministic

end DirectedFamilies

end CNNA.PillarA.ToC
