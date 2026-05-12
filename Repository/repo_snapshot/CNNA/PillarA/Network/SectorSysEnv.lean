import CNNA.PillarA.Network.SectorChannels

set_option autoImplicit false

namespace CNNA.PillarA.Network

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.Sectors
open CNNA.PillarA.Coupling

universe u

inductive SysEnvKind where
  | system
  | interface
  | environment
  deriving DecidableEq, Repr

structure SectorSysEnvStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SectorChannelsStrong Cell T

abbrev SectorSysEnvStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SectorSysEnvStrong (Cell := Cell) T

namespace SectorSysEnvStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : SectorSysEnvStrong Cell T)
    (hsource : X.source = Y.source) :
    X = Y := by
  cases X with
  | mk sourceX =>
    cases Y with
    | mk sourceY =>
      cases hsource
      rfl

def cast (h : T = U) (X : SectorSysEnvStrong Cell T) :
    SectorSysEnvStrong Cell U := by
  cases h
  exact X

theorem cast_rfl (X : SectorSysEnvStrong Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofSectorChannels (C : SectorChannelsStrong Cell T) :
    SectorSysEnvStrong Cell T where
  source := C

theorem ofSectorChannels_source (C : SectorChannelsStrong Cell T) :
    (ofSectorChannels C).source = C := by
  rfl

def channels (X : SectorSysEnvStrong Cell T) : SectorChannelsStrong Cell T :=
  X.source

def generalized (X : SectorSysEnvStrong Cell T) : GeneralizedDtNStrong Cell T :=
  X.source.generalized

def split (X : SectorSysEnvStrong Cell T) : SectorSplitStrong Cell T :=
  X.source.split

def binary (X : SectorSysEnvStrong Cell T) : CNNA.PillarA.DtN.DtNStrong Cell T :=
  X.source.binary

def cutoff (_ : SectorSysEnvStrong Cell T) : Nat :=
  T.cutoff

def toCoupledKind : SysEnvKind → CoupledSectorKind
  | .system => .bright
  | .interface => .interface
  | .environment => .dark

def region (X : SectorSysEnvStrong Cell T) : SysEnvKind → RegionCore Cell T
  | .system => X.split.brightRegion
  | .interface => X.split.interfaceRegion
  | .environment => X.split.darkRegion

def boundaryPorts (X : SectorSysEnvStrong Cell T) : SysEnvKind → BoundaryPorts Cell T
  | .system => X.source.sectorBoundaryPorts .bright
  | .interface => X.source.sectorBoundaryPorts .interface
  | .environment => X.source.sectorBoundaryPorts .dark

def regionCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : Finset (Cell L) :=
  X.generalized.regionCarrier (toCoupledKind K) L

def boundaryCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : Finset (Cell L) :=
  X.source.boundaryCarrier (toCoupledKind K) L

def sectorCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : Finset (Cell L) :=
  X.source.sectorCarrier (toCoupledKind K) L

def interiorCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : Finset (Cell L) :=
  (X.boundaryPorts K).interiorCarrier L

def regionSlice (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : LayerSlice Cell :=
  (X.region K).slice L

def boundarySlice (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : BoundarySlice Cell :=
  (X.boundaryPorts K).slice L

def interiorSlice (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := X.interiorCarrier K L }

abbrev boundaryVertex (X : SectorSysEnvStrong Cell T) :=
  X.source.boundaryVertex

abbrev sectorBoundaryVertex (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) :=
  SectorChannelsStrong.sectorBoundaryVertex X.source (toCoupledKind K)

abbrev boundaryPotential (X : SectorSysEnvStrong Cell T) :=
  X.boundaryVertex → ℝ

abbrev sectorPotential (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) :=
  X.sectorBoundaryVertex K → ℝ

def channel (X : SectorSysEnvStrong Cell T)
    (src dst : SysEnvKind) :
    Matrix (X.sectorBoundaryVertex src) (X.sectorBoundaryVertex dst) ℝ :=
  X.source.channel (toCoupledKind src) (toCoupledKind dst)

def restrict (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (φ : X.boundaryPotential) :
    X.sectorPotential K :=
  X.source.restrict (toCoupledKind K) φ

def glue (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (φ : X.sectorPotential K) :
    X.boundaryPotential :=
  X.source.glue (toCoupledKind K) φ

def noOuterEnvironment (X : SectorSysEnvStrong Cell T) : Prop :=
  X.source.noOuterEnvironment

def hasOuterEnvironment (X : SectorSysEnvStrong Cell T) : Prop :=
  X.source.hasOuterEnvironment

def rootCentered (X : SectorSysEnvStrong Cell T) : Prop :=
  X.noOuterEnvironment

def windowed (X : SectorSysEnvStrong Cell T) : Prop :=
  X.hasOuterEnvironment

def systemRegion (X : SectorSysEnvStrong Cell T) : RegionCore Cell T :=
  X.region .system

def interfaceRegion (X : SectorSysEnvStrong Cell T) : RegionCore Cell T :=
  X.region .interface

def environmentRegion (X : SectorSysEnvStrong Cell T) : RegionCore Cell T :=
  X.region .environment

def systemBoundaryPorts (X : SectorSysEnvStrong Cell T) : BoundaryPorts Cell T :=
  X.boundaryPorts .system

def interfaceBoundaryPorts (X : SectorSysEnvStrong Cell T) : BoundaryPorts Cell T :=
  X.boundaryPorts .interface

def environmentBoundaryPorts (X : SectorSysEnvStrong Cell T) : BoundaryPorts Cell T :=
  X.boundaryPorts .environment

def systemToInterface (X : SectorSysEnvStrong Cell T) :
    Matrix (X.sectorBoundaryVertex .system) (X.sectorBoundaryVertex .interface) ℝ :=
  X.channel .system .interface

def interfaceToSystem (X : SectorSysEnvStrong Cell T) :
    Matrix (X.sectorBoundaryVertex .interface) (X.sectorBoundaryVertex .system) ℝ :=
  X.channel .interface .system

def systemToEnvironment (X : SectorSysEnvStrong Cell T) :
    Matrix (X.sectorBoundaryVertex .system) (X.sectorBoundaryVertex .environment) ℝ :=
  X.channel .system .environment

def environmentToSystem (X : SectorSysEnvStrong Cell T) :
    Matrix (X.sectorBoundaryVertex .environment) (X.sectorBoundaryVertex .system) ℝ :=
  X.channel .environment .system

def interfaceToEnvironment (X : SectorSysEnvStrong Cell T) :
    Matrix (X.sectorBoundaryVertex .interface) (X.sectorBoundaryVertex .environment) ℝ :=
  X.channel .interface .environment

def environmentToInterface (X : SectorSysEnvStrong Cell T) :
    Matrix (X.sectorBoundaryVertex .environment) (X.sectorBoundaryVertex .interface) ℝ :=
  X.channel .environment .interface

def topRegionCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) : Finset (Cell T.cutoff) :=
  X.regionCarrier K T.cutoff

def topBoundaryCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) : Finset (Cell T.cutoff) :=
  X.boundaryCarrier K T.cutoff

def topSectorCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) : Finset (Cell T.cutoff) :=
  X.sectorCarrier K T.cutoff

def topInteriorCarrier (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) : Finset (Cell T.cutoff) :=
  X.interiorCarrier K T.cutoff

theorem channels_eq_source (X : SectorSysEnvStrong Cell T) :
    X.channels = X.source := by
  rfl

theorem generalized_eq_source_generalized (X : SectorSysEnvStrong Cell T) :
    X.generalized = X.source.generalized := by
  rfl

theorem split_eq_source_split (X : SectorSysEnvStrong Cell T) :
    X.split = X.source.split := by
  rfl

theorem binary_eq_source_binary (X : SectorSysEnvStrong Cell T) :
    X.binary = X.source.binary := by
  rfl

theorem region_system (X : SectorSysEnvStrong Cell T) :
    X.region .system = X.split.brightRegion := by
  rfl

theorem region_interface (X : SectorSysEnvStrong Cell T) :
    X.region .interface = X.split.interfaceRegion := by
  rfl

theorem region_environment (X : SectorSysEnvStrong Cell T) :
    X.region .environment = X.split.darkRegion := by
  rfl

theorem boundaryPorts_system (X : SectorSysEnvStrong Cell T) :
    X.boundaryPorts .system = X.source.sectorBoundaryPorts .bright := by
  rfl

theorem boundaryPorts_interface (X : SectorSysEnvStrong Cell T) :
    X.boundaryPorts .interface = X.source.sectorBoundaryPorts .interface := by
  rfl

theorem boundaryPorts_environment (X : SectorSysEnvStrong Cell T) :
    X.boundaryPorts .environment = X.source.sectorBoundaryPorts .dark := by
  rfl

theorem regionCarrier_subset (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) (L : Nat) :
    X.regionCarrier K L ⊆ T.carrier L := by
  exact X.generalized.regionCarrier_subset (toCoupledKind K) L

theorem boundaryCarrier_subset_regionCarrier (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (L : Nat) :
    X.boundaryCarrier K L ⊆ X.regionCarrier K L := by
  exact X.generalized.boundaryCarrier_subset_regionCarrier (toCoupledKind K) L

theorem interiorCarrier_subset_regionCarrier (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (L : Nat) :
    X.interiorCarrier K L ⊆ X.regionCarrier K L := by
  cases K with
  | system =>
      simpa [interiorCarrier, regionCarrier, boundaryPorts, toCoupledKind, generalized]
        using X.generalized.interiorCarrier_subset_regionCarrier CoupledSectorKind.bright L
  | interface =>
      simpa [interiorCarrier, regionCarrier, boundaryPorts, toCoupledKind, generalized]
        using X.generalized.interiorCarrier_subset_regionCarrier CoupledSectorKind.interface L
  | environment =>
      simpa [interiorCarrier, regionCarrier, boundaryPorts, toCoupledKind, generalized]
        using X.generalized.interiorCarrier_subset_regionCarrier CoupledSectorKind.dark L

theorem sectorCarrier_subset_regionCarrier (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (L : Nat) :
    X.sectorCarrier K L ⊆ X.regionCarrier K L := by
  rw [sectorCarrier, regionCarrier]
  cases K with
  | system =>
      exact X.generalized.split.brightSector_subset_brightCarrier L
  | interface =>
      intro x hx
      exact hx
  | environment =>
      exact X.generalized.split.darkSector_subset_darkCarrier L

theorem sectorCarrier_subset_ambient (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (L : Nat) :
    X.sectorCarrier K L ⊆ T.carrier L := by
  intro x hx
  exact X.regionCarrier_subset K L (X.sectorCarrier_subset_regionCarrier K L hx)

theorem channel_apply (X : SectorSysEnvStrong Cell T)
    (src dst : SysEnvKind)
    (i : X.sectorBoundaryVertex src)
    (j : X.sectorBoundaryVertex dst) :
    X.channel src dst i j = X.source.generalized.boundaryOperator i.1 j.1 := by
  exact SectorChannelsStrong.channel_apply X.source (toCoupledKind src) (toCoupledKind dst) i j

theorem restrict_glue (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (φ : X.sectorPotential K) :
    X.restrict K (X.glue K φ) = φ := by
  exact X.source.restrict_glue (toCoupledKind K) φ

theorem glue_apply_of_mem (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (φ : X.sectorPotential K)
    {v : X.boundaryVertex} (hv : X.source.generalized.boundaryVertexInSector (toCoupledKind K) v) :
    X.glue K φ v = φ ⟨v, hv⟩ := by
  exact X.source.glue_apply_of_mem (toCoupledKind K) φ hv

theorem glue_apply_of_not_mem (X : SectorSysEnvStrong Cell T)
    (K : SysEnvKind) (φ : X.sectorPotential K)
    {v : X.boundaryVertex} (hv : ¬ X.source.generalized.boundaryVertexInSector (toCoupledKind K) v) :
    X.glue K φ v = 0 := by
  exact X.source.glue_apply_of_not_mem (toCoupledKind K) φ hv

theorem noOuterEnvironment_iff_environmentCarrier_empty (X : SectorSysEnvStrong Cell T) :
    X.noOuterEnvironment ↔ ∀ L : Nat, X.regionCarrier .environment L = ∅ := by
  simpa [regionCarrier, toCoupledKind] using
    X.split.noOuterEnvironment_iff_darkCarrier_empty

theorem hasOuterEnvironment_iff_exists_environmentCarrier_nonempty
    (X : SectorSysEnvStrong Cell T) :
    X.hasOuterEnvironment ↔ ∃ L : Nat, (X.regionCarrier .environment L).Nonempty := by
  simpa [regionCarrier, toCoupledKind] using
    X.split.hasOuterEnvironment_iff_exists_darkCarrier_nonempty

theorem rootCentered_iff_noOuterEnvironment (X : SectorSysEnvStrong Cell T) :
    X.rootCentered ↔ X.noOuterEnvironment := by
  rfl

theorem windowed_iff_hasOuterEnvironment (X : SectorSysEnvStrong Cell T) :
    X.windowed ↔ X.hasOuterEnvironment := by
  rfl

theorem topRegionCarrier_eq (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) :
    X.topRegionCarrier K = X.regionCarrier K T.cutoff := by
  rfl

theorem topBoundaryCarrier_eq (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) :
    X.topBoundaryCarrier K = X.boundaryCarrier K T.cutoff := by
  rfl

theorem topSectorCarrier_eq (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) :
    X.topSectorCarrier K = X.sectorCarrier K T.cutoff := by
  rfl

theorem topInteriorCarrier_eq (X : SectorSysEnvStrong Cell T) (K : SysEnvKind) :
    X.topInteriorCarrier K = X.interiorCarrier K T.cutoff := by
  rfl

end SectorSysEnvStrong

end CNNA.PillarA.Network
