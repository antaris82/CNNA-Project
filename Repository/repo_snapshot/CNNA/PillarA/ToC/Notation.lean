import CNNA.PillarA.ToC.ConcreteIdeal
import CNNA.PillarA.ToC.Concrete

set_option autoImplicit false

namespace CNNA.PillarA.ToC


abbrev ReferenceIdealCellOf (b : Nat) (L : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.ReferenceCell b L

abbrev ReferenceIdealAddrOf (b : Nat) (L : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.ReferenceAddr b L

abbrev ReferenceIdealThreadOf (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceThread b

abbrev ReferenceIdealFamilyOf (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceFamily b

abbrev ReferenceAddressThreadOf (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceAddressThread b

abbrev ReferenceAddressFamilyOf (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceAddressFamily b


abbrev RootSliceOf (Cell : Nat → Type _) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.rootSlice (Cell := Cell)

abbrev EmptyOriginOf (Cell : Nat → Type _) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.emptyOrigin (Cell := Cell)

abbrev ParentSliceOf
    (Cell : Nat → Type _) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (c : Cell (L + 1)) :=
  CNNA.PillarA.ToC.parentSlice (Cell := Cell) c

abbrev ChildSliceOf
    (Cell : Nat → Type _) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (c : Cell L) :=
  CNNA.PillarA.ToC.childSlice (Cell := Cell) c

scoped notation "𝓓∞[" Cell "]" => CNNA.PillarA.ToC.DirectedFamily (Cell := Cell)
scoped notation "𝓓ref∞[" b "]" => CNNA.PillarA.ToC.ConcreteIdeal.referenceFamily b
scoped notation "𝓐ref∞[" b "]" => CNNA.PillarA.ToC.ConcreteIdeal.referenceAddressFamily b
scoped notation "𝓣∞[" Cell "]" => CNNA.PillarA.ToC.IdealThread Cell
scoped notation "𝓐∞[" Cell "," Addr "]" =>
  CNNA.PillarA.ToC.AddressPresentation.AddressFamily (Cell := Cell) (Addr := Addr)
scoped notation "𝓣addr∞[" Cell "," Addr "]" =>
  CNNA.PillarA.ToC.AddressPresentation.AddressThread (Cell := Cell) (Addr := Addr)
scoped notation a " ≼[" Cell "," Addr "] " b =>
  CNNA.PillarA.ToC.AddressPresentation.PrefixRel Cell Addr a b

end CNNA.PillarA.ToC
