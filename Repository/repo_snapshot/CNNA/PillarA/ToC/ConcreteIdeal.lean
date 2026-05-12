import CNNA.PillarA.ToC.IdealAddressEquiv
import CNNA.PillarA.Foundation.ConcreteSubstrate

set_option autoImplicit false

namespace CNNA.PillarA.ToC

open CNNA.PillarA.Foundation

namespace ConcreteIdeal

abbrev ReferenceCell (b : Nat) (L : Nat) : Type :=
  ConcreteSubstrate.RegularCell b L

structure ReferenceAddr (b : Nat) (L : Nat) where
  toCell : ReferenceCell b L
  deriving DecidableEq, Repr

namespace ReferenceAddr

variable {b L M N : Nat}

def ofCell {b L : Nat} (c : ReferenceCell b L) : ReferenceAddr b L :=
  ⟨c⟩

theorem toCell_ofCell {b L : Nat} (c : ReferenceCell b L) :
    (ofCell c).toCell = c := by
  rfl

theorem ofCell_toCell {b L : Nat} (a : ReferenceAddr b L) :
    ofCell a.toCell = a := by
  cases a
  rfl

@[ext] theorem ext {b L : Nat} {a₁ a₂ : ReferenceAddr b L}
    (h : a₁.toCell = a₂.toCell) : a₁ = a₂ := by
  cases a₁
  cases a₂
  cases h
  rfl

def equivCell (b : Nat) (L : Nat) : ReferenceAddr b L ≃ ReferenceCell b L where
  toFun := ReferenceAddr.toCell
  invFun := ofCell
  left_inv := ofCell_toCell
  right_inv := toCell_ofCell

instance instFintype (b : Nat) (L : Nat) : Fintype (ReferenceAddr b L) := by
  exact Fintype.ofEquiv (ReferenceCell b L) (equivCell b L).symm

end ReferenceAddr

variable {b : Nat}

instance instAddressPresentationReference (b : Nat) :
    AddressPresentation (ReferenceCell b) (ReferenceAddr b) where
  instDecEq := by
    intro L
    infer_instance
  instFintype := by
    intro L
    infer_instance
  root := ReferenceAddr.ofCell (ConcreteSubstrate.root b)
  parent := fun {L} a => ReferenceAddr.ofCell (ConcreteSubstrate.parent a.toCell)
  children := fun {L} a =>
    (ConcreteSubstrate.children a.toCell).image ReferenceAddr.ofCell
  parent_eq_iff_mem_children := by
    intro L a c
    constructor
    · intro h
      have hcell : ConcreteSubstrate.parent c.toCell = a.toCell := by
        exact congrArg ReferenceAddr.toCell h
      have hmem : c.toCell ∈ ConcreteSubstrate.children a.toCell :=
        (ConcreteSubstrate.mem_children_iff (p := a.toCell) (c := c.toCell)).2 hcell
      exact Finset.mem_image.mpr ⟨c.toCell, hmem, ReferenceAddr.ofCell_toCell c⟩
    · intro h
      rcases Finset.mem_image.mp h with ⟨c0, hc0, hEq⟩
      have hcToCell : c0 = c.toCell := by
        have hto : ReferenceAddr.toCell (ReferenceAddr.ofCell c0) = ReferenceAddr.toCell c := by
          exact congrArg ReferenceAddr.toCell hEq
        rw [ReferenceAddr.toCell_ofCell] at hto
        exact hto
      have hparent : ConcreteSubstrate.parent c0 = a.toCell :=
        (ConcreteSubstrate.mem_children_iff (p := a.toCell) (c := c0)).1 hc0
      apply ReferenceAddr.ext
      calc
        ConcreteSubstrate.parent c.toCell = ConcreteSubstrate.parent c0 := by
          rw [hcToCell.symm]
        _ = a.toCell := hparent
  children_nonempty := by
    intro L a
    rcases ConcreteSubstrate.children_nonempty a.toCell with ⟨c, hc⟩
    refine ⟨ReferenceAddr.ofCell c, ?_⟩
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  root_eq := by
    intro a
    apply ReferenceAddr.ext
    exact ConcreteSubstrate.root_eq b a.toCell
  ancestor := by
    intro L M h a
    refine ReferenceAddr.ofCell ?_
    exact fun i => a.toCell ⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩
  ancestor_refl := by
    intro L a
    apply ReferenceAddr.ext
    funext i
    have hidx : (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_refl L)⟩ : Fin L) = i := by
      apply Fin.ext
      rfl
    exact congrArg a.toCell hidx
  ancestor_step := by
    intro L a
    apply ReferenceAddr.ext
    funext i
    have hidx :
        (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_succ L)⟩ : Fin (L + 1)) = i.castSucc := by
      apply Fin.ext
      rfl
    exact congrArg a.toCell hidx
  ancestor_comp := by
    intro L M N hLM hMN a
    apply ReferenceAddr.ext
    funext i
    have hidx :
        (⟨(⟨i.1, Nat.lt_of_lt_of_le i.2 hLM⟩ : Fin M).1,
          Nat.lt_of_lt_of_le (⟨i.1, Nat.lt_of_lt_of_le i.2 hLM⟩ : Fin M).2 hMN⟩ : Fin N) =
        (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_trans hLM hMN)⟩ : Fin N) := by
      apply Fin.ext
      rfl
    exact congrArg a.toCell hidx
  ancestor_root := by
    intro L a
    apply ReferenceAddr.ext
    exact ConcreteSubstrate.root_eq b _
  cellOf := fun {L} a => a.toCell
  addressOf := fun {L} c => ReferenceAddr.ofCell c
  cellOf_addressOf := by
    intro L c
    rfl
  addressOf_cellOf := by
    intro L a
    exact ReferenceAddr.ofCell_toCell a
  parent_respects_cells := by
    intro L a
    change ConcreteSubstrate.parent a.toCell ∈ ({ConcreteSubstrate.parent a.toCell} : Finset (ReferenceCell b L))
    simp

instance instSubstrateClassReferenceAddr (b : Nat) : SubstrateClass (ReferenceAddr b) :=
  AddressPresentation.addressSubstrate (Cell := ReferenceCell b) (Addr := ReferenceAddr b)

instance instIdealAddressEquivReference (b : Nat) :
    IdealAddressEquiv (ReferenceCell b) (ReferenceAddr b) where
  child_mem_children_iff := by
    intro L p c
    change c ∈ ConcreteSubstrate.children p ↔
      ReferenceAddr.ofCell c ∈ (ConcreteSubstrate.children p).image ReferenceAddr.ofCell
    constructor
    · intro hc
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · intro hc
      rcases Finset.mem_image.mp hc with ⟨c0, hc0, hEq⟩
      have hc0eq : c0 = c := by
        have hto : ReferenceAddr.toCell (ReferenceAddr.ofCell c0) =
            ReferenceAddr.toCell (ReferenceAddr.ofCell c) := by
          exact congrArg ReferenceAddr.toCell hEq
        rw [ReferenceAddr.toCell_ofCell, ReferenceAddr.toCell_ofCell] at hto
        exact hto
      simpa [hc0eq] using hc0
  toAddressPresentation := instAddressPresentationReference b

def referenceThread (b : Nat) : IdealThread (ReferenceCell b) :=
  ConcreteSubstrate.zeroThread b

def referenceFamily (b : Nat) : DirectedFamily (Cell := ReferenceCell b) :=
  (referenceThread b).family

def referenceAddressThread (b : Nat) :
    AddressPresentation.AddressThread (Cell := ReferenceCell b) (Addr := ReferenceAddr b) where
  cell := fun L => ReferenceAddr.ofCell (ConcreteSubstrate.zeroCell b L)
  coh := by
    intro L
    change ReferenceAddr.ofCell (ConcreteSubstrate.parent (ConcreteSubstrate.zeroCell b (L + 1))) ∈
      ({ReferenceAddr.ofCell (ConcreteSubstrate.parent (ConcreteSubstrate.zeroCell b (L + 1)))} :
        Finset (ReferenceAddr b L))
    simp

def referenceAddressFamily (b : Nat) :
    AddressPresentation.AddressFamily (Cell := ReferenceCell b) (Addr := ReferenceAddr b) :=
  (referenceAddressThread b).family

theorem referenceFamily_rooted (b : Nat) :
    (referenceFamily b).carrier 0 = SubstrateClass.rootLayer (Cell := ReferenceCell b) := by
  exact (referenceThread b).rooted_carrier

theorem referenceCellOf_addressOf {b L : Nat} (c : ReferenceCell b L) :
    AddressPresentation.cellOf (Cell := ReferenceCell b) (Addr := ReferenceAddr b)
      (AddressPresentation.addressOf (Cell := ReferenceCell b) (Addr := ReferenceAddr b) c) = c := by
  rfl

theorem referenceAddressOf_cellOf {b L : Nat} (a : ReferenceAddr b L) :
    AddressPresentation.addressOf (Cell := ReferenceCell b) (Addr := ReferenceAddr b)
      (AddressPresentation.cellOf (Cell := ReferenceCell b) (Addr := ReferenceAddr b) a) = a := by
  exact ReferenceAddr.ofCell_toCell a

theorem referenceEncodeDecode {b L : Nat} (a : ReferenceAddr b L) :
    IdealAddressEquiv.encode (Cell := ReferenceCell b) (Addr := ReferenceAddr b)
      (IdealAddressEquiv.decode (Cell := ReferenceCell b) (Addr := ReferenceAddr b) a) = a := by
  exact IdealAddressEquiv.encode_decode (Cell := ReferenceCell b) (Addr := ReferenceAddr b) a

theorem referenceDecodeEncode {b L : Nat} (c : ReferenceCell b L) :
    IdealAddressEquiv.decode (Cell := ReferenceCell b) (Addr := ReferenceAddr b)
      (IdealAddressEquiv.encode (Cell := ReferenceCell b) (Addr := ReferenceAddr b) c) = c := by
  exact IdealAddressEquiv.decode_encode (Cell := ReferenceCell b) (Addr := ReferenceAddr b) c

end ConcreteIdeal

end CNNA.PillarA.ToC
