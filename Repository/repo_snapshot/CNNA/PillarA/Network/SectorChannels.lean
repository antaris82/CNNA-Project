import CNNA.PillarA.Coupling.GeneralizedDtN

set_option autoImplicit false

namespace CNNA.PillarA.Network

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.Sectors
open CNNA.PillarA.Coupling

universe u

structure SectorChannelsStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : GeneralizedDtNStrong Cell T

abbrev SectorChannelsStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SectorChannelsStrong (Cell := Cell) T

namespace SectorChannelsStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (C D : SectorChannelsStrong Cell T)
    (hsource : C.source = D.source) :
    C = D := by
  cases C with
  | mk sourceC =>
    cases D with
    | mk sourceD =>
      cases hsource
      rfl

def cast (h : T = U) (C : SectorChannelsStrong Cell T) :
    SectorChannelsStrong Cell U := by
  cases h
  exact C

theorem cast_rfl (C : SectorChannelsStrong Cell T) :
    cast (Cell := Cell) rfl C = C := by
  rfl

def ofGeneralizedDtN (G : GeneralizedDtNStrong Cell T) :
    SectorChannelsStrong Cell T where
  source := G

theorem ofGeneralizedDtN_source (G : GeneralizedDtNStrong Cell T) :
    (ofGeneralizedDtN G).source = G := by
  rfl

def generalized (C : SectorChannelsStrong Cell T) : GeneralizedDtNStrong Cell T :=
  C.source

def split (C : SectorChannelsStrong Cell T) : SectorSplitStrong Cell T :=
  C.source.split

def binary (C : SectorChannelsStrong Cell T) : CNNA.PillarA.DtN.DtNStrong Cell T :=
  C.source.binary

def cutoff (_ : SectorChannelsStrong Cell T) : Nat :=
  T.cutoff

def noOuterEnvironment (C : SectorChannelsStrong Cell T) : Prop :=
  C.source.noOuterEnvironment

def hasOuterEnvironment (C : SectorChannelsStrong Cell T) : Prop :=
  C.source.hasOuterEnvironment

abbrev boundaryVertex (C : SectorChannelsStrong Cell T) :=
  C.source.boundaryVertex

abbrev sectorBoundaryVertex (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) :=
  GeneralizedDtNStrong.SectorBoundaryVertex C.source K

abbrev boundaryPotential (C : SectorChannelsStrong Cell T) :=
  C.boundaryVertex → ℝ

abbrev sectorPotential (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) :=
  C.sectorBoundaryVertex K → ℝ

def sectorBoundaryPorts (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) : BoundaryPorts Cell T :=
  C.source.sectorBoundaryPorts K

def boundaryCarrier (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : Finset (Cell L) :=
  C.source.boundaryCarrier K L

def sectorCarrier (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : Finset (Cell L) :=
  C.source.sectorCarrier K L

def channel (C : SectorChannelsStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (C.sectorBoundaryVertex src) (C.sectorBoundaryVertex dst) ℝ :=
  C.source.restrictedBlock src dst

def restrict (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (φ : C.boundaryPotential) :
    C.sectorPotential K :=
  C.source.restrictToSector K φ

def glue (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (φ : C.sectorPotential K) :
    C.boundaryPotential :=
  C.source.glueFromSector K φ

def brightBright (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .bright) (C.sectorBoundaryVertex .bright) ℝ :=
  C.channel .bright .bright

def brightInterface (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .bright) (C.sectorBoundaryVertex .interface) ℝ :=
  C.channel .bright .interface

def brightDark (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .bright) (C.sectorBoundaryVertex .dark) ℝ :=
  C.channel .bright .dark

def interfaceBright (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .interface) (C.sectorBoundaryVertex .bright) ℝ :=
  C.channel .interface .bright

def interfaceInterface (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .interface) (C.sectorBoundaryVertex .interface) ℝ :=
  C.channel .interface .interface

def interfaceDark (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .interface) (C.sectorBoundaryVertex .dark) ℝ :=
  C.channel .interface .dark

def darkBright (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .dark) (C.sectorBoundaryVertex .bright) ℝ :=
  C.channel .dark .bright

def darkInterface (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .dark) (C.sectorBoundaryVertex .interface) ℝ :=
  C.channel .dark .interface

def darkDark (C : SectorChannelsStrong Cell T) :
    Matrix (C.sectorBoundaryVertex .dark) (C.sectorBoundaryVertex .dark) ℝ :=
  C.channel .dark .dark

theorem generalized_eq_source (C : SectorChannelsStrong Cell T) :
    C.generalized = C.source := by
  rfl

theorem split_eq_source_split (C : SectorChannelsStrong Cell T) :
    C.split = C.source.split := by
  rfl

theorem binary_eq_source_binary (C : SectorChannelsStrong Cell T) :
    C.binary = C.source.binary := by
  rfl

theorem sectorBoundaryPorts_eq_source
    (C : SectorChannelsStrong Cell T) (K : CoupledSectorKind) :
    C.sectorBoundaryPorts K = C.source.sectorBoundaryPorts K := by
  rfl

theorem boundaryCarrier_eq_source
    (C : SectorChannelsStrong Cell T) (K : CoupledSectorKind) (L : Nat) :
    C.boundaryCarrier K L = C.source.boundaryCarrier K L := by
  rfl

theorem sectorCarrier_eq_source
    (C : SectorChannelsStrong Cell T) (K : CoupledSectorKind) (L : Nat) :
    C.sectorCarrier K L = C.source.sectorCarrier K L := by
  rfl

theorem channel_apply (C : SectorChannelsStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : C.sectorBoundaryVertex src)
    (j : C.sectorBoundaryVertex dst) :
    C.channel src dst i j = C.source.boundaryOperator i.1 j.1 := by
  exact GeneralizedDtNStrong.restrictedBlock_apply C.source src dst i j

theorem restrict_glue (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (φ : C.sectorPotential K) :
    C.restrict K (C.glue K φ) = φ := by
  exact GeneralizedDtNStrong.restrictToSector_glueFromSector C.source K φ

theorem glue_apply_of_mem (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (φ : C.sectorPotential K)
    {v : C.boundaryVertex} (hv : C.source.boundaryVertexInSector K v) :
    C.glue K φ v = φ ⟨v, hv⟩ := by
  exact GeneralizedDtNStrong.glueFromSector_apply_of_mem C.source K φ hv

theorem glue_apply_of_not_mem (C : SectorChannelsStrong Cell T)
    (K : CoupledSectorKind) (φ : C.sectorPotential K)
    {v : C.boundaryVertex} (hv : ¬ C.source.boundaryVertexInSector K v) :
    C.glue K φ v = 0 := by
  exact GeneralizedDtNStrong.glueFromSector_apply_of_not_mem C.source K φ hv

theorem noOuterEnvironment_iff_source (C : SectorChannelsStrong Cell T) :
    C.noOuterEnvironment ↔ C.source.noOuterEnvironment := by
  rfl

theorem hasOuterEnvironment_iff_source (C : SectorChannelsStrong Cell T) :
    C.hasOuterEnvironment ↔ C.source.hasOuterEnvironment := by
  rfl

end SectorChannelsStrong


namespace StrengtheningS7

open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6
open CNNA.PillarA.Coupling.StrengtheningS7

def referenceFullSectorChannels (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    : SectorChannelsStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  SectorChannelsStrong.ofGeneralizedDtN <|
    referenceFullGeneralizedDtN b p wp rp

def variationFullSectorChannels (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    : SectorChannelsStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  SectorChannelsStrong.ofGeneralizedDtN <|
    variationFullGeneralizedDtN β p wp rp

end StrengtheningS7

end CNNA.PillarA.Network
