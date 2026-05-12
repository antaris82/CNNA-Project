import CNNA.PillarA.Handoff.Core.SectorExport

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

structure Step1StrongCore (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SectorExportStrong Cell T

abbrev Step1StrongCoreOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  Step1StrongCore (Cell := Cell) T

namespace Step1StrongCore

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : Step1StrongCore Cell T)
    (hsource : X.source = Y.source) :
    X = Y := by
  cases X with
  | mk sourceX =>
    cases Y with
    | mk sourceY =>
      cases hsource
      rfl

def cast (h : T = U) (X : Step1StrongCore Cell T) :
    Step1StrongCore Cell U := by
  cases h
  exact X

theorem cast_rfl (X : Step1StrongCore Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofSectorExport (X : SectorExportStrong Cell T) :
    Step1StrongCore Cell T where
  source := X

theorem ofSectorExport_source (X : SectorExportStrong Cell T) :
    (ofSectorExport X).source = X := by
  rfl

def exportData (X : Step1StrongCore Cell T) : SectorExportStrong Cell T :=
  X.source

def carrier (X : Step1StrongCore Cell T) : InfiniteCarrierStrong Cell T :=
  X.exportData.carrier

def regularization (X : Step1StrongCore Cell T) : RegularizationClosureStrong Cell T :=
  X.exportData.regularization

def schur (X : Step1StrongCore Cell T) : MultiSchurStrong Cell T :=
  X.exportData.schur

def regionNet (X : Step1StrongCore Cell T) : RegionNetStrong Cell T :=
  X.exportData.regionNet

def split (X : Step1StrongCore Cell T) : SectorSplitStrong Cell T :=
  X.exportData.split

def approximant (X : Step1StrongCore Cell T) : ApproximantStrong Cell T :=
  X.exportData.approximant

def ideal (X : Step1StrongCore Cell T) : DirectedFamily (Cell := Cell) :=
  X.exportData.ideal

def cutoff (X : Step1StrongCore Cell T) : Nat :=
  X.exportData.cutoff

def dirichlet (X : Step1StrongCore Cell T) : DirichletLaplacianStrong Cell T :=
  X.exportData.dirichlet

def binary (X : Step1StrongCore Cell T) : DtNStrong Cell T :=
  X.exportData.binary

def closureStabilizedBinary (X : Step1StrongCore Cell T) : DtNStabilizedStrong Cell T :=
  X.exportData.closureStabilizedBinary

def generalized (X : Step1StrongCore Cell T) : GeneralizedDtNStrong Cell T :=
  X.exportData.generalized

def couplingStabilizedBinary (X : Step1StrongCore Cell T) : DtNStabilizedStrong Cell T :=
  X.exportData.couplingStabilizedBinary

def selector (X : Step1StrongCore Cell T) : BranchingSelectorStrong Cell T :=
  X.exportData.selector

def witness (X : Step1StrongCore Cell T) : BranchingWitnessStrong Cell T :=
  X.exportData.witness

def branching (X : Step1StrongCore Cell T) : SelectedBranchingStrong Cell T :=
  X.exportData.branching

def uv (X : Step1StrongCore Cell T) : UVSpectralSelectorStrong Cell T :=
  X.exportData.uv

def selectedLevel (X : Step1StrongCore Cell T) : Nat :=
  X.exportData.selectedLevel

def candidateLevels (X : Step1StrongCore Cell T) : Finset Nat :=
  X.exportData.candidateLevels

def irLevels (X : Step1StrongCore Cell T) : Finset Nat :=
  X.exportData.irLevels

def uvLevels (X : Step1StrongCore Cell T) : Finset Nat :=
  X.exportData.uvLevels

def hasUVTail (X : Step1StrongCore Cell T) : Prop :=
  X.exportData.hasUVTail

def epsilon (X : Step1StrongCore Cell T) : ℝ :=
  X.exportData.epsilon

def regularizationShift (X : Step1StrongCore Cell T) : ℝ :=
  X.exportData.regularizationShift

def noOuterEnvironment (X : Step1StrongCore Cell T) : Prop :=
  X.exportData.noOuterEnvironment

def hasOuterEnvironment (X : Step1StrongCore Cell T) : Prop :=
  X.exportData.hasOuterEnvironment

def stableCarrier (X : Step1StrongCore Cell T) (L : Nat) : Finset (Cell L) :=
  X.exportData.stableCarrier L

def idealCarrier (X : Step1StrongCore Cell T) (L : Nat) : Finset (Cell L) :=
  X.exportData.idealCarrier L

def brightRegion (X : Step1StrongCore Cell T) : RegionCore Cell T :=
  X.exportData.brightRegion

def interfaceRegion (X : Step1StrongCore Cell T) : RegionCore Cell T :=
  X.exportData.interfaceRegion

def darkRegion (X : Step1StrongCore Cell T) : RegionCore Cell T :=
  X.exportData.darkRegion

theorem exportData_eq_source (X : Step1StrongCore Cell T) :
    X.exportData = X.source := by
  rfl

theorem carrier_eq_export_carrier (X : Step1StrongCore Cell T) :
    X.carrier = X.exportData.carrier := by
  rfl

theorem regularization_eq_export_regularization (X : Step1StrongCore Cell T) :
    X.regularization = X.exportData.regularization := by
  rfl

theorem schur_eq_export_schur (X : Step1StrongCore Cell T) :
    X.schur = X.exportData.schur := by
  rfl

theorem regionNet_eq_export_regionNet (X : Step1StrongCore Cell T) :
    X.regionNet = X.exportData.regionNet := by
  rfl

theorem split_eq_export_split (X : Step1StrongCore Cell T) :
    X.split = X.exportData.split := by
  rfl

theorem approximant_eq_export_approximant (X : Step1StrongCore Cell T) :
    X.approximant = X.exportData.approximant := by
  rfl

theorem dirichlet_eq_export_dirichlet (X : Step1StrongCore Cell T) :
    X.dirichlet = X.exportData.dirichlet := by
  rfl

theorem binary_eq_export_binary (X : Step1StrongCore Cell T) :
    X.binary = X.exportData.binary := by
  rfl

theorem closureStabilizedBinary_eq_export_closureStabilizedBinary
    (X : Step1StrongCore Cell T) :
    X.closureStabilizedBinary = X.exportData.closureStabilizedBinary := by
  rfl

theorem couplingStabilizedBinary_eq_export_couplingStabilizedBinary
    (X : Step1StrongCore Cell T) :
    X.couplingStabilizedBinary = X.exportData.couplingStabilizedBinary := by
  rfl

theorem generalized_eq_export_generalized (X : Step1StrongCore Cell T) :
    X.generalized = X.exportData.generalized := by
  rfl

theorem selectedLevel_eq_export_selectedLevel (X : Step1StrongCore Cell T) :
    X.selectedLevel = X.exportData.selectedLevel := by
  rfl

theorem candidateLevels_eq_export_candidateLevels (X : Step1StrongCore Cell T) :
    X.candidateLevels = X.exportData.candidateLevels := by
  rfl

theorem irLevels_eq_export_irLevels (X : Step1StrongCore Cell T) :
    X.irLevels = X.exportData.irLevels := by
  rfl

theorem uvLevels_eq_export_uvLevels (X : Step1StrongCore Cell T) :
    X.uvLevels = X.exportData.uvLevels := by
  rfl

theorem epsilon_eq_export_epsilon (X : Step1StrongCore Cell T) :
    X.epsilon = X.exportData.epsilon := by
  rfl

theorem regularizationShift_eq_export_regularizationShift (X : Step1StrongCore Cell T) :
    X.regularizationShift = X.exportData.regularizationShift := by
  rfl

theorem regularization_split_eq_split (X : Step1StrongCore Cell T) :
    X.regularization.split = X.split := by
  exact X.exportData.regularization_split_eq_split

theorem schur_split_eq_split (X : Step1StrongCore Cell T) :
    X.schur.split = X.split := by
  exact X.exportData.schur_split_eq_split

theorem selectedLevelAdmissible (X : Step1StrongCore Cell T) :
    X.selectedLevel ∈ X.candidateLevels := by
  exact X.exportData.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (X : Step1StrongCore Cell T) :
    X.selectedLevel ≤ X.cutoff := by
  exact X.exportData.selectedLevel_le_cutoff

theorem epsilon_pos (X : Step1StrongCore Cell T) :
    0 < X.epsilon := by
  exact X.exportData.epsilon_pos

theorem regularizationShift_pos (X : Step1StrongCore Cell T) :
    0 < X.regularizationShift := by
  exact X.exportData.regularizationShift_pos

theorem regularizationShift_ge_epsilon (X : Step1StrongCore Cell T) :
    X.epsilon ≤ X.regularizationShift := by
  exact X.exportData.regularizationShift_ge_epsilon

theorem hasUVTail_iff_nonempty (X : Step1StrongCore Cell T) :
    X.hasUVTail ↔ X.uvLevels.Nonempty := by
  exact X.exportData.hasUVTail_iff_nonempty

theorem noOuterEnvironment_iff_split (X : Step1StrongCore Cell T) :
    X.noOuterEnvironment ↔ X.split.noOuterEnvironment := by
  exact X.exportData.noOuterEnvironment_iff_split

theorem hasOuterEnvironment_iff_split (X : Step1StrongCore Cell T) :
    X.hasOuterEnvironment ↔ X.split.hasOuterEnvironment := by
  exact X.exportData.hasOuterEnvironment_iff_split

theorem stable_eq_truncate (X : Step1StrongCore Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.exportData.stable_eq_truncate

theorem stableCarrier_eq_ideal_of_le
    (X : Step1StrongCore Cell T) {L : Nat} (hL : L ≤ X.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  exact X.exportData.stableCarrier_eq_ideal_of_le hL

theorem stableCarrier_eq_empty_of_gt
    (X : Step1StrongCore Cell T) {L : Nat} (hL : X.cutoff < L) :
    X.stableCarrier L = ∅ := by
  exact X.exportData.stableCarrier_eq_empty_of_gt hL

end Step1StrongCore

end CNNA.PillarA.Handoff
