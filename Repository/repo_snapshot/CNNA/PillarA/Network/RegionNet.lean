import CNNA.PillarA.Sectors.SectorSplit

set_option autoImplicit false

namespace CNNA.PillarA.Network

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.Sectors

universe u

inductive RegionKind where
  | bright
  | interface
  | dark
  deriving DecidableEq, Repr

structure RegionNetStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SectorSplitStrong Cell T

abbrev RegionNetStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  RegionNetStrong (Cell := Cell) T

namespace RegionNetStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (N M : RegionNetStrong Cell T)
    (hsource : N.source = M.source) :
    N = M := by
  cases N with
  | mk sourceN =>
    cases M with
    | mk sourceM =>
      cases hsource
      rfl

def cast (h : T = U) (N : RegionNetStrong Cell T) :
    RegionNetStrong Cell U := by
  cases h
  exact N

theorem cast_rfl (N : RegionNetStrong Cell T) :
    cast (Cell := Cell) rfl N = N := by
  rfl

def ofSectorSplit (S : SectorSplitStrong Cell T) : RegionNetStrong Cell T where
  source := S

theorem ofSectorSplit_source (S : SectorSplitStrong Cell T) :
    (ofSectorSplit S).source = S := by
  rfl

def split (N : RegionNetStrong Cell T) : SectorSplitStrong Cell T :=
  N.source

def brightRegion (N : RegionNetStrong Cell T) : RegionCore Cell T :=
  N.source.brightRegion

def interfaceRegion (N : RegionNetStrong Cell T) : RegionCore Cell T :=
  N.source.interfaceRegion

def darkRegion (N : RegionNetStrong Cell T) : RegionCore Cell T :=
  N.source.darkRegion

def region (N : RegionNetStrong Cell T) : RegionKind → RegionCore Cell T
  | .bright => N.brightRegion
  | .interface => N.interfaceRegion
  | .dark => N.darkRegion

def brightBoundaryPorts (N : RegionNetStrong Cell T) : BoundaryPorts Cell T :=
  N.source.brightBoundaryPorts

def interfaceBoundaryPorts (N : RegionNetStrong Cell T) : BoundaryPorts Cell T :=
  N.source.interfaceBoundaryPorts

def darkBoundaryPorts (N : RegionNetStrong Cell T) : BoundaryPorts Cell T :=
  N.source.darkBoundaryPorts

def boundaryPorts (N : RegionNetStrong Cell T) : RegionKind → BoundaryPorts Cell T
  | .bright => N.brightBoundaryPorts
  | .interface => N.interfaceBoundaryPorts
  | .dark => N.darkBoundaryPorts

def brightRegionCarrier (N : RegionNetStrong Cell T) (L : Nat) : Finset (Cell L) :=
  N.source.brightCarrier L

def interfaceRegionCarrier (N : RegionNetStrong Cell T) (L : Nat) : Finset (Cell L) :=
  N.source.interfaceCarrier L

def darkRegionCarrier (N : RegionNetStrong Cell T) (L : Nat) : Finset (Cell L) :=
  N.source.darkCarrier L

def regionCarrier (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  match K with
  | .bright => N.brightRegionCarrier L
  | .interface => N.interfaceRegionCarrier L
  | .dark => N.darkRegionCarrier L

def brightSectorCarrier (N : RegionNetStrong Cell T) (L : Nat) : Finset (Cell L) :=
  N.source.brightSectorCarrier L

def interfaceSectorCarrier (N : RegionNetStrong Cell T) (L : Nat) : Finset (Cell L) :=
  N.source.interfaceCarrier L

def darkSectorCarrier (N : RegionNetStrong Cell T) (L : Nat) : Finset (Cell L) :=
  N.source.darkSectorCarrier L

def sectorCarrier (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  match K with
  | .bright => N.brightSectorCarrier L
  | .interface => N.interfaceSectorCarrier L
  | .dark => N.darkSectorCarrier L

def ports (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  (N.boundaryPorts K).ports L

def interiorCarrier (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  (N.boundaryPorts K).interiorCarrier L

def regionSlice (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : LayerSlice Cell :=
  (N.region K).slice L

def boundarySlice (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : BoundarySlice Cell :=
  (N.boundaryPorts K).slice L

def interiorSlice (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := N.interiorCarrier K L }

def cutoff (_ : RegionNetStrong Cell T) : Nat :=
  T.cutoff

def topRegionCarrier (N : RegionNetStrong Cell T) (K : RegionKind) : Finset (Cell T.cutoff) :=
  N.regionCarrier K T.cutoff

def topSectorCarrier (N : RegionNetStrong Cell T) (K : RegionKind) : Finset (Cell T.cutoff) :=
  N.sectorCarrier K T.cutoff

def topPorts (N : RegionNetStrong Cell T) (K : RegionKind) : Finset (Cell T.cutoff) :=
  N.ports K T.cutoff

def topInteriorCarrier (N : RegionNetStrong Cell T) (K : RegionKind) : Finset (Cell T.cutoff) :=
  N.interiorCarrier K T.cutoff

def noOuterEnvironment (N : RegionNetStrong Cell T) : Prop :=
  N.source.noOuterEnvironment

def hasOuterEnvironment (N : RegionNetStrong Cell T) : Prop :=
  N.source.hasOuterEnvironment

def rootCentered (N : RegionNetStrong Cell T) : Prop :=
  N.noOuterEnvironment

def windowed (N : RegionNetStrong Cell T) : Prop :=
  N.hasOuterEnvironment

theorem split_eq_source (N : RegionNetStrong Cell T) :
    N.split = N.source := by
  rfl

theorem brightRegion_eq_split_brightRegion (N : RegionNetStrong Cell T) :
    N.brightRegion = N.source.brightRegion := by
  rfl

theorem interfaceRegion_eq_split_interfaceRegion (N : RegionNetStrong Cell T) :
    N.interfaceRegion = N.source.interfaceRegion := by
  rfl

theorem darkRegion_eq_split_darkRegion (N : RegionNetStrong Cell T) :
    N.darkRegion = N.source.darkRegion := by
  rfl

theorem brightBoundaryPorts_eq_split_brightBoundaryPorts (N : RegionNetStrong Cell T) :
    N.brightBoundaryPorts = N.source.brightBoundaryPorts := by
  rfl

theorem interfaceBoundaryPorts_eq_split_interfaceBoundaryPorts (N : RegionNetStrong Cell T) :
    N.interfaceBoundaryPorts = N.source.interfaceBoundaryPorts := by
  rfl

theorem darkBoundaryPorts_eq_split_darkBoundaryPorts (N : RegionNetStrong Cell T) :
    N.darkBoundaryPorts = N.source.darkBoundaryPorts := by
  rfl

theorem region_bright (N : RegionNetStrong Cell T) :
    N.region .bright = N.brightRegion := by
  rfl

theorem region_interface (N : RegionNetStrong Cell T) :
    N.region .interface = N.interfaceRegion := by
  rfl

theorem region_dark (N : RegionNetStrong Cell T) :
    N.region .dark = N.darkRegion := by
  rfl

theorem boundaryPorts_bright (N : RegionNetStrong Cell T) :
    N.boundaryPorts .bright = N.brightBoundaryPorts := by
  rfl

theorem boundaryPorts_interface (N : RegionNetStrong Cell T) :
    N.boundaryPorts .interface = N.interfaceBoundaryPorts := by
  rfl

theorem boundaryPorts_dark (N : RegionNetStrong Cell T) :
    N.boundaryPorts .dark = N.darkBoundaryPorts := by
  rfl

theorem regionCarrier_subset (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    N.regionCarrier K L ⊆ T.carrier L := by
  cases K with
  | bright =>
      exact N.source.brightPatch.carrier_subset L
  | interface =>
      exact N.source.interface_subset_ambient L
  | dark =>
      exact N.source.darkFamily.carrier_subset L

theorem ports_subset_regionCarrier (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    N.ports K L ⊆ N.regionCarrier K L := by
  cases K with
  | bright =>
      exact N.source.brightPatch.boundary_subset_carrier L
  | interface =>
      exact N.source.interfaceBoundaryPorts.ports_subset_carrier L
  | dark =>
      exact N.source.darkFamily.boundary_subset_carrier L

theorem interiorCarrier_subset_regionCarrier
    (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    N.interiorCarrier K L ⊆ N.regionCarrier K L := by
  cases K with
  | bright =>
      exact N.source.brightPatch.interior_subset_carrier L
  | interface =>
      exact N.source.interfaceBoundaryPorts.interiorCarrier_subset_carrier L
  | dark =>
      exact N.source.darkFamily.interior_subset_carrier L

theorem sectorCarrier_subset_regionCarrier
    (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    N.sectorCarrier K L ⊆ N.regionCarrier K L := by
  cases K with
  | bright =>
      exact N.source.brightSector_subset_brightCarrier L
  | interface =>
      intro x hx
      exact hx
  | dark =>
      exact N.source.darkSector_subset_darkCarrier L

theorem sectorCarrier_subset_ambient
    (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    N.sectorCarrier K L ⊆ T.carrier L := by
  intro x hx
  exact N.regionCarrier_subset K L (N.sectorCarrier_subset_regionCarrier K L hx)

theorem regionSlice_level (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    (N.regionSlice K L).level = L := by
  cases K with
  | bright =>
      exact N.brightRegion.slice_level L
  | interface =>
      exact N.interfaceRegion.slice_level L
  | dark =>
      exact N.darkRegion.slice_level L

theorem boundarySlice_level (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    (N.boundarySlice K L).level = L := by
  cases K with
  | bright =>
      exact N.brightBoundaryPorts.slice_level L
  | interface =>
      exact N.interfaceBoundaryPorts.slice_level L
  | dark =>
      exact N.darkBoundaryPorts.slice_level L

theorem interiorSlice_level (N : RegionNetStrong Cell T) (K : RegionKind) (L : Nat) :
    (N.interiorSlice K L).level = L := by
  rfl

theorem topRegionCarrier_eq (N : RegionNetStrong Cell T) (K : RegionKind) :
    N.topRegionCarrier K = N.regionCarrier K T.cutoff := by
  rfl

theorem topSectorCarrier_eq (N : RegionNetStrong Cell T) (K : RegionKind) :
    N.topSectorCarrier K = N.sectorCarrier K T.cutoff := by
  rfl

theorem topPorts_eq (N : RegionNetStrong Cell T) (K : RegionKind) :
    N.topPorts K = N.ports K T.cutoff := by
  rfl

theorem topInteriorCarrier_eq (N : RegionNetStrong Cell T) (K : RegionKind) :
    N.topInteriorCarrier K = N.interiorCarrier K T.cutoff := by
  rfl

theorem rootCentered_iff_noOuterEnvironment (N : RegionNetStrong Cell T) :
    N.rootCentered ↔ N.noOuterEnvironment := by
  rfl

theorem windowed_iff_hasOuterEnvironment (N : RegionNetStrong Cell T) :
    N.windowed ↔ N.hasOuterEnvironment := by
  rfl

theorem noOuterEnvironment_iff_darkRegionCarrier_empty (N : RegionNetStrong Cell T) :
    N.noOuterEnvironment ↔ ∀ L : Nat, N.darkRegionCarrier L = ∅ := by
  exact N.source.noOuterEnvironment_iff_darkCarrier_empty

theorem hasOuterEnvironment_iff_exists_darkRegionCarrier_nonempty
    (N : RegionNetStrong Cell T) :
    N.hasOuterEnvironment ↔ ∃ L : Nat, (N.darkRegionCarrier L).Nonempty := by
  exact N.source.hasOuterEnvironment_iff_exists_darkCarrier_nonempty

theorem sectorCover (N : RegionNetStrong Cell T) (L : Nat) :
    N.sectorCarrier .bright L ∪ N.sectorCarrier .interface L ∪ N.sectorCarrier .dark L =
      T.carrier L := by
  exact N.source.sectorCover L

theorem sectorPartition (N : RegionNetStrong Cell T) (L : Nat) :
    N.sectorCarrier .bright L ∪ N.sectorCarrier .interface L ∪ N.sectorCarrier .dark L =
        T.carrier L ∧
      Disjoint (N.sectorCarrier .bright L) (N.sectorCarrier .interface L) ∧
      Disjoint (N.sectorCarrier .bright L) (N.sectorCarrier .dark L) ∧
      Disjoint (N.sectorCarrier .interface L) (N.sectorCarrier .dark L) := by
  exact N.source.sectorPartition L


end RegionNetStrong

namespace StrengtheningS7

open CNNA.PillarA.DtN
open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6

private def regionNetFromStabilized
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (K : DtNStabilizedStrong Cell T) : RegionNetStrong Cell T :=
  RegionNetStrong.ofSectorSplit <|
    SectorSplitStrong.ofComplementSectorFamily <|
      ComplementSectorFamilyStrong.ofBranchPatch <|
        BranchPatchStrong.ofDtNStabilized K

def referenceFullRegionNet (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    : RegionNetStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  regionNetFromStabilized (referenceFullDtNStabilized b p wp rp)

def variationFullRegionNet (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    : RegionNetStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  regionNetFromStabilized (variationFullDtNStabilized β p wp rp)

end StrengtheningS7

end CNNA.PillarA.Network
