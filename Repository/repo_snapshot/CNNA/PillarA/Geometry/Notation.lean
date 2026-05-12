import CNNA.PillarA.Geometry.SpacetimePaths

set_option autoImplicit false

namespace CNNA.PillarA.Geometry

abbrev LCPDepth
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) :=
  CNNA.PillarA.Geometry.lcpDepth (Cell := Cell) (Addr := Addr) a b

abbrev LCPAddress
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) :=
  CNNA.PillarA.Geometry.lcpAddress (Cell := Cell) (Addr := Addr) a b

abbrev LCPCell
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) :=
  CNNA.PillarA.Geometry.lcpCell (Cell := Cell) (Addr := Addr) a b

abbrev BranchDistance
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) :=
  CNNA.PillarA.Geometry.branchDistance (Cell := Cell) (Addr := Addr) a b

abbrev FoliatedAddress
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.BundledAddress (Cell := Cell) (Addr := Addr)

abbrev FoliationTime
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.foliationTime (Cell := Cell) (Addr := Addr)

abbrev FoliationLayer
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.foliationLayer (Cell := Cell) (Addr := Addr)

abbrev BundledPrefix
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr]
    (x y : CNNA.PillarA.Geometry.BundledAddress (Cell := Cell) (Addr := Addr)) :=
  CNNA.PillarA.Geometry.bundledPrefix (Cell := Cell) (Addr := Addr) x y

abbrev AddressWorldline
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.Worldline (Cell := Cell) (Addr := Addr)

abbrev AddressWorldTube
    (Cell : Nat → Type _) (Addr : Nat → Type _)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.WorldTube (Cell := Cell) (Addr := Addr)

scoped notation "τ[" Cell "," Addr "]" =>
  CNNA.PillarA.Geometry.foliationTime (Cell := Cell) (Addr := Addr)

scoped notation "Σ[" Cell "," Addr ";" n "]" =>
  CNNA.PillarA.Geometry.foliationLayer (Cell := Cell) (Addr := Addr) n

end CNNA.PillarA.Geometry
