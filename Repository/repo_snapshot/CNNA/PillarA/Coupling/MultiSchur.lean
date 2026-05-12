import CNNA.PillarA.Coupling.GeneralizedDtN

set_option autoImplicit false

namespace CNNA.PillarA.Coupling

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors

universe u

inductive InterfaceEliminationMode where
  | explicitInverse
  | reduction
  | fallback
  deriving DecidableEq, Repr

private structure InternalInterfaceInverse
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (G : GeneralizedDtNStrong Cell T) where
  inv : Matrix
    (GeneralizedDtNStrong.SectorBoundaryVertex G .interface)
    (GeneralizedDtNStrong.SectorBoundaryVertex G .interface) ℝ
  inv_ok : TwoSidedInv
    (GeneralizedDtNStrong.stabilizedRestrictedBlock G .interface .interface)
    inv

class InterfaceEliminationData
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (G : GeneralizedDtNStrong Cell T) where
  eliminationMode : InterfaceEliminationMode
  interfaceInverse : Matrix
    (GeneralizedDtNStrong.SectorBoundaryVertex G .interface)
    (GeneralizedDtNStrong.SectorBoundaryVertex G .interface) ℝ
  interfaceInverse_spec : TwoSidedInv
    (GeneralizedDtNStrong.stabilizedRestrictedBlock G .interface .interface)
    interfaceInverse

namespace InterfaceEliminationData

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

private def ofInternalInverse
    (G : GeneralizedDtNStrong Cell T)
    (w : InternalInterfaceInverse G)
    (mode : InterfaceEliminationMode := InterfaceEliminationMode.explicitInverse) :
    InterfaceEliminationData G where
  eliminationMode := mode
  interfaceInverse := w.inv
  interfaceInverse_spec := w.inv_ok

end InterfaceEliminationData

structure MultiSchurStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : GeneralizedDtNStrong Cell T
  eliminationMode : InterfaceEliminationMode
  interfaceInverse :
    Matrix
      (GeneralizedDtNStrong.SectorBoundaryVertex source .interface)
      (GeneralizedDtNStrong.SectorBoundaryVertex source .interface) ℝ
  interfaceInverse_ok :
    TwoSidedInv
      (GeneralizedDtNStrong.stabilizedRestrictedBlock source .interface .interface)
      interfaceInverse

abbrev MultiSchurStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  MultiSchurStrong (Cell := Cell) T

namespace MultiSchurStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (M N : MultiSchurStrong Cell T)
    (hsource : M.source = N.source)
    (hmode : M.eliminationMode = N.eliminationMode)
    (hinv : HEq M.interfaceInverse N.interfaceInverse) :
    M = N := by
  cases M with
  | mk sourceM modeM invM okM =>
    cases N with
    | mk sourceN modeN invN okN =>
      cases hsource
      cases hmode
      cases hinv
      have hok : okM = okN := Subsingleton.elim _ _
      cases hok
      rfl

def cast (h : T = U) (M : MultiSchurStrong Cell T) :
    MultiSchurStrong Cell U := by
  cases h
  exact M

theorem cast_rfl (M : MultiSchurStrong Cell T) :
    cast (Cell := Cell) rfl M = M := by
  rfl

def ofEliminationData
    (G : GeneralizedDtNStrong Cell T)
    [edata : InterfaceEliminationData G] :
    MultiSchurStrong Cell T where
  source := G
  eliminationMode := edata.eliminationMode
  interfaceInverse := edata.interfaceInverse
  interfaceInverse_ok := edata.interfaceInverse_spec

theorem ofEliminationData_source
    (G : GeneralizedDtNStrong Cell T)
    [InterfaceEliminationData G] :
    (ofEliminationData G).source = G := by
  rfl

def generalized (M : MultiSchurStrong Cell T) : GeneralizedDtNStrong Cell T :=
  M.source

def split (M : MultiSchurStrong Cell T) : SectorSplitStrong Cell T :=
  M.source.split

def binary (M : MultiSchurStrong Cell T) : DtNStrong Cell T :=
  M.source.binary

def stabilizedBinary (M : MultiSchurStrong Cell T) : DtNStabilizedStrong Cell T :=
  M.source.stabilizedBinary

def dirichlet (M : MultiSchurStrong Cell T) : DirichletLaplacianStrong Cell T :=
  M.source.dirichlet

def approximant (M : MultiSchurStrong Cell T) : ApproximantStrong Cell T :=
  M.source.approximant

abbrev boundaryVertex (M : MultiSchurStrong Cell T) :=
  M.source.boundaryVertex

abbrev boundaryPotential (M : MultiSchurStrong Cell T) :=
  M.boundaryVertex → ℝ

abbrev sectorBoundaryVertex (M : MultiSchurStrong Cell T)
    (K : CoupledSectorKind) :=
  GeneralizedDtNStrong.SectorBoundaryVertex M.source K

abbrev sectorPotential (M : MultiSchurStrong Cell T)
    (K : CoupledSectorKind) :=
  M.sectorBoundaryVertex K → ℝ

abbrev brightBoundaryVertex (M : MultiSchurStrong Cell T) :=
  M.sectorBoundaryVertex .bright

abbrev interfaceBoundaryVertex (M : MultiSchurStrong Cell T) :=
  M.sectorBoundaryVertex .interface

abbrev darkBoundaryVertex (M : MultiSchurStrong Cell T) :=
  M.sectorBoundaryVertex .dark

abbrev brightPotential (M : MultiSchurStrong Cell T) :=
  M.sectorPotential .bright

abbrev interfacePotential (M : MultiSchurStrong Cell T) :=
  M.sectorPotential .interface

abbrev darkPotential (M : MultiSchurStrong Cell T) :=
  M.sectorPotential .dark

abbrev reducedPotential (M : MultiSchurStrong Cell T) :=
  M.brightPotential × M.darkPotential

def cutoff (_ : MultiSchurStrong Cell T) : Nat :=
  T.cutoff

def noOuterEnvironment (M : MultiSchurStrong Cell T) : Prop :=
  M.source.noOuterEnvironment

def hasOuterEnvironment (M : MultiSchurStrong Cell T) : Prop :=
  M.source.hasOuterEnvironment

def restrict (M : MultiSchurStrong Cell T)
    (K : CoupledSectorKind) (φ : M.boundaryPotential) :
    M.sectorPotential K :=
  M.source.restrictToSector K φ

def glue (M : MultiSchurStrong Cell T)
    (K : CoupledSectorKind) (φ : M.sectorPotential K) :
    M.boundaryPotential :=
  M.source.glueFromSector K φ

def restrictBright (M : MultiSchurStrong Cell T)
    (φ : M.boundaryPotential) : M.brightPotential :=
  M.restrict .bright φ

def restrictInterface (M : MultiSchurStrong Cell T)
    (φ : M.boundaryPotential) : M.interfacePotential :=
  M.restrict .interface φ

def restrictDark (M : MultiSchurStrong Cell T)
    (φ : M.boundaryPotential) : M.darkPotential :=
  M.restrict .dark φ

def glueBright (M : MultiSchurStrong Cell T)
    (φ : M.brightPotential) : M.boundaryPotential :=
  M.glue .bright φ

def glueInterface (M : MultiSchurStrong Cell T)
    (φ : M.interfacePotential) : M.boundaryPotential :=
  M.glue .interface φ

def glueDark (M : MultiSchurStrong Cell T)
    (φ : M.darkPotential) : M.boundaryPotential :=
  M.glue .dark φ

def rawBlock (M : MultiSchurStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (M.sectorBoundaryVertex src) (M.sectorBoundaryVertex dst) ℝ :=
  M.source.rawRestrictedBlock src dst

def stabilizedBlock (M : MultiSchurStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (M.sectorBoundaryVertex src) (M.sectorBoundaryVertex dst) ℝ :=
  M.source.stabilizedRestrictedBlock src dst

def block (M : MultiSchurStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (M.sectorBoundaryVertex src) (M.sectorBoundaryVertex dst) ℝ :=
  M.stabilizedBlock src dst

def rawBrightBrightBlock (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.rawBlock .bright .bright

def rawBrightInterfaceBlock (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.interfaceBoundaryVertex ℝ :=
  M.rawBlock .bright .interface

def rawBrightDarkBlock (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.rawBlock .bright .dark

def rawInterfaceBrightBlock (M : MultiSchurStrong Cell T) :
    Matrix M.interfaceBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.rawBlock .interface .bright

def rawInterfaceBlock (M : MultiSchurStrong Cell T) :
    Matrix M.interfaceBoundaryVertex M.interfaceBoundaryVertex ℝ :=
  M.rawBlock .interface .interface

def rawInterfaceDarkBlock (M : MultiSchurStrong Cell T) :
    Matrix M.interfaceBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.rawBlock .interface .dark

def rawDarkBrightBlock (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.rawBlock .dark .bright

def rawDarkInterfaceBlock (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.interfaceBoundaryVertex ℝ :=
  M.rawBlock .dark .interface

def rawDarkDarkBlock (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.rawBlock .dark .dark

def brightBrightBlock (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.block .bright .bright

def brightInterfaceBlock (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.interfaceBoundaryVertex ℝ :=
  M.block .bright .interface

def brightDarkBlock (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.block .bright .dark

def interfaceBrightBlock (M : MultiSchurStrong Cell T) :
    Matrix M.interfaceBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.block .interface .bright

def interfaceBlock (M : MultiSchurStrong Cell T) :
    Matrix M.interfaceBoundaryVertex M.interfaceBoundaryVertex ℝ :=
  M.block .interface .interface

def interfaceDarkBlock (M : MultiSchurStrong Cell T) :
    Matrix M.interfaceBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.block .interface .dark

def darkBrightBlock (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.block .dark .bright

def darkInterfaceBlock (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.interfaceBoundaryVertex ℝ :=
  M.block .dark .interface

def darkDarkBlock (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.block .dark .dark

def brightBrightSchur (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.brightBrightBlock - M.brightInterfaceBlock * M.interfaceInverse * M.interfaceBrightBlock

def brightDarkSchur (M : MultiSchurStrong Cell T) :
    Matrix M.brightBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.brightDarkBlock - M.brightInterfaceBlock * M.interfaceInverse * M.interfaceDarkBlock

def darkBrightSchur (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.brightBoundaryVertex ℝ :=
  M.darkBrightBlock - M.darkInterfaceBlock * M.interfaceInverse * M.interfaceBrightBlock

def darkDarkSchur (M : MultiSchurStrong Cell T) :
    Matrix M.darkBoundaryVertex M.darkBoundaryVertex ℝ :=
  M.darkDarkBlock - M.darkInterfaceBlock * M.interfaceInverse * M.interfaceDarkBlock

def reducedFlux (M : MultiSchurStrong Cell T)
    (φ : M.reducedPotential) :
    M.reducedPotential :=
  let φB : M.brightPotential := φ.1
  let φD : M.darkPotential := φ.2
  ( fun i => (M.brightBrightSchur.mulVec φB) i + (M.brightDarkSchur.mulVec φD) i
  , fun i => (M.darkBrightSchur.mulVec φB) i + (M.darkDarkSchur.mulVec φD) i )

def glueReducedPotential (M : MultiSchurStrong Cell T)
    (φ : M.reducedPotential) :
    M.boundaryPotential :=
  fun v => M.glueBright φ.1 v + M.glueDark φ.2 v

def restrictReducedPotential (M : MultiSchurStrong Cell T)
    (φ : M.boundaryPotential) :
    M.reducedPotential :=
  (M.restrictBright φ, M.restrictDark φ)

theorem restrict_glue (M : MultiSchurStrong Cell T)
    (K : CoupledSectorKind) (φ : M.sectorPotential K) :
    M.restrict K (M.glue K φ) = φ := by
  exact M.source.restrictToSector_glueFromSector K φ

theorem restrictBright_glueBright (M : MultiSchurStrong Cell T)
    (φ : M.brightPotential) :
    M.restrictBright (M.glueBright φ) = φ := by
  exact M.restrict_glue .bright φ

theorem restrictInterface_glueInterface (M : MultiSchurStrong Cell T)
    (φ : M.interfacePotential) :
    M.restrictInterface (M.glueInterface φ) = φ := by
  exact M.restrict_glue .interface φ

theorem restrictDark_glueDark (M : MultiSchurStrong Cell T)
    (φ : M.darkPotential) :
    M.restrictDark (M.glueDark φ) = φ := by
  exact M.restrict_glue .dark φ

theorem interfaceInverse_left_inv (M : MultiSchurStrong Cell T) :
    M.interfaceBlock * M.interfaceInverse = 1 := by
  exact M.interfaceInverse_ok.left_inv

theorem interfaceInverse_right_inv (M : MultiSchurStrong Cell T) :
    M.interfaceInverse * M.interfaceBlock = 1 := by
  exact M.interfaceInverse_ok.right_inv

theorem rawBlock_eq_source_rawRestrictedBlock (M : MultiSchurStrong Cell T)
    (src dst : CoupledSectorKind) :
    M.rawBlock src dst = M.source.rawRestrictedBlock src dst := by
  rfl

theorem stabilizedBlock_eq_source_stabilizedRestrictedBlock (M : MultiSchurStrong Cell T)
    (src dst : CoupledSectorKind) :
    M.stabilizedBlock src dst = M.source.stabilizedRestrictedBlock src dst := by
  rfl

theorem block_eq_source_stabilizedRestrictedBlock (M : MultiSchurStrong Cell T)
    (src dst : CoupledSectorKind) :
    M.block src dst = M.source.stabilizedRestrictedBlock src dst := by
  rfl

theorem brightBrightSchur_def (M : MultiSchurStrong Cell T) :
    M.brightBrightSchur =
      M.brightBrightBlock -
        M.brightInterfaceBlock * M.interfaceInverse * M.interfaceBrightBlock := by
  rfl

theorem brightDarkSchur_def (M : MultiSchurStrong Cell T) :
    M.brightDarkSchur =
      M.brightDarkBlock -
        M.brightInterfaceBlock * M.interfaceInverse * M.interfaceDarkBlock := by
  rfl

theorem darkBrightSchur_def (M : MultiSchurStrong Cell T) :
    M.darkBrightSchur =
      M.darkBrightBlock -
        M.darkInterfaceBlock * M.interfaceInverse * M.interfaceBrightBlock := by
  rfl

theorem darkDarkSchur_def (M : MultiSchurStrong Cell T) :
    M.darkDarkSchur =
      M.darkDarkBlock -
        M.darkInterfaceBlock * M.interfaceInverse * M.interfaceDarkBlock := by
  rfl

end MultiSchurStrong

namespace StrengtheningS7

open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6

abbrev ReferenceInterfaceEliminationData (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp] :=
  InterfaceEliminationData (referenceFullGeneralizedDtN b p wp rp)

abbrev VariationInterfaceEliminationData (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp] :=
  InterfaceEliminationData (variationFullGeneralizedDtN β p wp rp)

def referenceFullMultiSchur (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp]
    : MultiSchurStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  MultiSchurStrong.ofEliminationData (referenceFullGeneralizedDtN b p wp rp)

def variationFullMultiSchur (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    [VariationInterfaceEliminationData β p wp rp]
    : MultiSchurStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  MultiSchurStrong.ofEliminationData (variationFullGeneralizedDtN β p wp rp)

end StrengtheningS7

end CNNA.PillarA.Coupling
