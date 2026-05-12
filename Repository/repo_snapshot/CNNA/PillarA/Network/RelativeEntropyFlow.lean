import CNNA.PillarA.Network.SectorSysEnv

open scoped BigOperators

set_option autoImplicit false

namespace CNNA.PillarA.Network

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.Sectors
open CNNA.PillarA.Coupling

universe u

structure RelativeEntropyFlowStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SectorSysEnvStrong Cell T

abbrev RelativeEntropyFlowStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  RelativeEntropyFlowStrong (Cell := Cell) T

namespace RelativeEntropyFlowStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (R S : RelativeEntropyFlowStrong Cell T)
    (hsource : R.source = S.source) :
    R = S := by
  cases R with
  | mk sourceR =>
    cases S with
    | mk sourceS =>
      cases hsource
      rfl

def cast (h : T = U) (R : RelativeEntropyFlowStrong Cell T) :
    RelativeEntropyFlowStrong Cell U := by
  cases h
  exact R

theorem cast_rfl (R : RelativeEntropyFlowStrong Cell T) :
    cast (Cell := Cell) rfl R = R := by
  rfl

def ofSectorSysEnv (X : SectorSysEnvStrong Cell T) :
    RelativeEntropyFlowStrong Cell T where
  source := X

theorem ofSectorSysEnv_source (X : SectorSysEnvStrong Cell T) :
    (ofSectorSysEnv X).source = X := by
  rfl

def sysenv (R : RelativeEntropyFlowStrong Cell T) : SectorSysEnvStrong Cell T :=
  R.source

def channels (R : RelativeEntropyFlowStrong Cell T) : SectorChannelsStrong Cell T :=
  R.source.channels

def generalized (R : RelativeEntropyFlowStrong Cell T) : GeneralizedDtNStrong Cell T :=
  R.source.generalized

def split (R : RelativeEntropyFlowStrong Cell T) : SectorSplitStrong Cell T :=
  R.source.split

def binary (R : RelativeEntropyFlowStrong Cell T) : CNNA.PillarA.DtN.DtNStrong Cell T :=
  R.source.binary

def cutoff (_ : RelativeEntropyFlowStrong Cell T) : Nat :=
  T.cutoff

abbrev boundaryVertex (R : RelativeEntropyFlowStrong Cell T) :=
  R.source.boundaryVertex

abbrev sectorBoundaryVertex (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) :=
  R.source.sectorBoundaryVertex K

abbrev boundaryPotential (R : RelativeEntropyFlowStrong Cell T) :=
  R.boundaryVertex → ℝ

abbrev sectorPotential (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) :=
  R.sectorBoundaryVertex K → ℝ

def channel (R : RelativeEntropyFlowStrong Cell T)
    (src dst : SysEnvKind) :
    Matrix (R.sectorBoundaryVertex src) (R.sectorBoundaryVertex dst) ℝ :=
  R.source.channel src dst

def restrict (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.boundaryPotential) :
    R.sectorPotential K :=
  R.source.restrict K φ

def glue (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.sectorPotential K) :
    R.boundaryPotential :=
  R.source.glue K φ

def sectorFlux (R : RelativeEntropyFlowStrong Cell T)
    (src dst : SysEnvKind) (φ : R.boundaryPotential) : ℝ :=
  ∑ i, ∑ j,
    (R.restrict src φ i) * (R.channel src dst i j) * (R.restrict dst φ j)

def systemSelfFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .system .system φ

def interfaceSelfFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .interface .interface φ

def environmentSelfFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .environment .environment φ

def systemInterfaceFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .system .interface φ

def interfaceSystemFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .interface .system φ

def systemEnvironmentFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .system .environment φ

def environmentSystemFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .environment .system φ

def interfaceEnvironmentFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .interface .environment φ

def environmentInterfaceFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.sectorFlux .environment .interface φ

def outgoingFlux (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.boundaryPotential) : ℝ :=
  match K with
  | .system =>
      R.systemInterfaceFlux φ + R.systemEnvironmentFlux φ
  | .interface =>
      R.interfaceSystemFlux φ + R.interfaceEnvironmentFlux φ
  | .environment =>
      R.environmentSystemFlux φ + R.environmentInterfaceFlux φ

def incomingFlux (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.boundaryPotential) : ℝ :=
  match K with
  | .system =>
      R.interfaceSystemFlux φ + R.environmentSystemFlux φ
  | .interface =>
      R.systemInterfaceFlux φ + R.environmentInterfaceFlux φ
  | .environment =>
      R.systemEnvironmentFlux φ + R.interfaceEnvironmentFlux φ

def netFlux (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.boundaryPotential) : ℝ :=
  R.outgoingFlux K φ - R.incomingFlux K φ

def totalCrossFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.systemInterfaceFlux φ + R.interfaceSystemFlux φ +
    R.systemEnvironmentFlux φ + R.environmentSystemFlux φ +
    R.interfaceEnvironmentFlux φ + R.environmentInterfaceFlux φ

def totalDiagonalFlux (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.systemSelfFlux φ + R.interfaceSelfFlux φ + R.environmentSelfFlux φ

def totalFluxBudget (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) : ℝ :=
  R.totalDiagonalFlux φ + R.totalCrossFlux φ

theorem sysenv_eq_source (R : RelativeEntropyFlowStrong Cell T) :
    R.sysenv = R.source := by
  rfl

theorem channels_eq_source_channels (R : RelativeEntropyFlowStrong Cell T) :
    R.channels = R.source.channels := by
  rfl

theorem generalized_eq_source_generalized (R : RelativeEntropyFlowStrong Cell T) :
    R.generalized = R.source.generalized := by
  rfl

theorem split_eq_source_split (R : RelativeEntropyFlowStrong Cell T) :
    R.split = R.source.split := by
  rfl

theorem binary_eq_source_binary (R : RelativeEntropyFlowStrong Cell T) :
    R.binary = R.source.binary := by
  rfl

theorem channel_eq_source (R : RelativeEntropyFlowStrong Cell T)
    (src dst : SysEnvKind) :
    R.channel src dst = R.source.channel src dst := by
  rfl

theorem restrict_eq_source (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.boundaryPotential) :
    R.restrict K φ = R.source.restrict K φ := by
  rfl

theorem glue_eq_source (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.sectorPotential K) :
    R.glue K φ = R.source.glue K φ := by
  rfl

theorem sectorFlux_eq (R : RelativeEntropyFlowStrong Cell T)
    (src dst : SysEnvKind) (φ : R.boundaryPotential) :
    R.sectorFlux src dst φ =
      ∑ i, ∑ j,
        (R.source.restrict src φ i) * (R.source.channel src dst i j) *
          (R.source.restrict dst φ j) := by
  rfl

theorem outgoingFlux_system (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.outgoingFlux .system φ =
      R.systemInterfaceFlux φ + R.systemEnvironmentFlux φ := by
  rfl

theorem outgoingFlux_interface (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.outgoingFlux .interface φ =
      R.interfaceSystemFlux φ + R.interfaceEnvironmentFlux φ := by
  rfl

theorem outgoingFlux_environment (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.outgoingFlux .environment φ =
      R.environmentSystemFlux φ + R.environmentInterfaceFlux φ := by
  rfl

theorem incomingFlux_system (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.incomingFlux .system φ =
      R.interfaceSystemFlux φ + R.environmentSystemFlux φ := by
  rfl

theorem incomingFlux_interface (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.incomingFlux .interface φ =
      R.systemInterfaceFlux φ + R.environmentInterfaceFlux φ := by
  rfl

theorem incomingFlux_environment (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.incomingFlux .environment φ =
      R.systemEnvironmentFlux φ + R.interfaceEnvironmentFlux φ := by
  rfl

theorem netFlux_eq (R : RelativeEntropyFlowStrong Cell T)
    (K : SysEnvKind) (φ : R.boundaryPotential) :
    R.netFlux K φ = R.outgoingFlux K φ - R.incomingFlux K φ := by
  rfl

theorem totalFluxBudget_eq (R : RelativeEntropyFlowStrong Cell T)
    (φ : R.boundaryPotential) :
    R.totalFluxBudget φ = R.totalDiagonalFlux φ + R.totalCrossFlux φ := by
  rfl

end RelativeEntropyFlowStrong

end CNNA.PillarA.Network
