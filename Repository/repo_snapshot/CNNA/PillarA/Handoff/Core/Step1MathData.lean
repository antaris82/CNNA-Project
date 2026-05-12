import CNNA.PillarA.Handoff.Core.Step1StrongCore

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

structure Step1MathDataStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : Step1StrongCore Cell T

abbrev Step1MathDataStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  Step1MathDataStrong (Cell := Cell) T

namespace Step1MathDataStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : Step1MathDataStrong Cell T)
    (hsource : X.source = Y.source) :
    X = Y := by
  cases X with
  | mk sourceX =>
    cases Y with
    | mk sourceY =>
      cases hsource
      rfl

def cast (h : T = U) (X : Step1MathDataStrong Cell T) :
    Step1MathDataStrong Cell U := by
  cases h
  exact X

theorem cast_rfl (X : Step1MathDataStrong Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofStrongCore (X : Step1StrongCore Cell T) :
    Step1MathDataStrong Cell T where
  source := X

theorem ofStrongCore_source (X : Step1StrongCore Cell T) :
    (ofStrongCore X).source = X := by
  rfl

def core (X : Step1MathDataStrong Cell T) : Step1StrongCore Cell T :=
  X.source

def exportData (X : Step1MathDataStrong Cell T) : SectorExportStrong Cell T :=
  X.core.exportData

def carrier (X : Step1MathDataStrong Cell T) : InfiniteCarrierStrong Cell T :=
  X.core.carrier

def regularization (X : Step1MathDataStrong Cell T) : RegularizationClosureStrong Cell T :=
  X.core.regularization

def schur (X : Step1MathDataStrong Cell T) : MultiSchurStrong Cell T :=
  X.core.schur

def regionNet (X : Step1MathDataStrong Cell T) : RegionNetStrong Cell T :=
  X.core.regionNet

def split (X : Step1MathDataStrong Cell T) : SectorSplitStrong Cell T :=
  X.core.split

def approximant (X : Step1MathDataStrong Cell T) : ApproximantStrong Cell T :=
  X.core.approximant

def ideal (X : Step1MathDataStrong Cell T) : DirectedFamily (Cell := Cell) :=
  X.core.ideal

def cutoff (X : Step1MathDataStrong Cell T) : Nat :=
  X.core.cutoff

def dirichlet (X : Step1MathDataStrong Cell T) : DirichletLaplacianStrong Cell T :=
  X.core.dirichlet

def binary (X : Step1MathDataStrong Cell T) : DtNStrong Cell T :=
  X.core.binary

def closureStabilizedBinary (X : Step1MathDataStrong Cell T) : DtNStabilizedStrong Cell T :=
  X.core.closureStabilizedBinary

def generalized (X : Step1MathDataStrong Cell T) : GeneralizedDtNStrong Cell T :=
  X.core.generalized

def couplingStabilizedBinary (X : Step1MathDataStrong Cell T) : DtNStabilizedStrong Cell T :=
  X.core.couplingStabilizedBinary

def selector (X : Step1MathDataStrong Cell T) : BranchingSelectorStrong Cell T :=
  X.core.selector

def witness (X : Step1MathDataStrong Cell T) : BranchingWitnessStrong Cell T :=
  X.core.witness

def branching (X : Step1MathDataStrong Cell T) : SelectedBranchingStrong Cell T :=
  X.core.branching

def uv (X : Step1MathDataStrong Cell T) : UVSpectralSelectorStrong Cell T :=
  X.core.uv

def selectedLevel (X : Step1MathDataStrong Cell T) : Nat :=
  X.core.selectedLevel

def candidateLevels (X : Step1MathDataStrong Cell T) : Finset Nat :=
  X.core.candidateLevels

def irLevels (X : Step1MathDataStrong Cell T) : Finset Nat :=
  X.core.irLevels

def uvLevels (X : Step1MathDataStrong Cell T) : Finset Nat :=
  X.core.uvLevels

def hasUVTail (X : Step1MathDataStrong Cell T) : Prop :=
  X.core.hasUVTail

def epsilon (X : Step1MathDataStrong Cell T) : ℝ :=
  X.core.epsilon

def regularizationShift (X : Step1MathDataStrong Cell T) : ℝ :=
  X.core.regularizationShift

def noOuterEnvironment (X : Step1MathDataStrong Cell T) : Prop :=
  X.core.noOuterEnvironment

def hasOuterEnvironment (X : Step1MathDataStrong Cell T) : Prop :=
  X.core.hasOuterEnvironment

def stableCarrier (X : Step1MathDataStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.core.stableCarrier L

def idealCarrier (X : Step1MathDataStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.core.idealCarrier L

def brightRegion (X : Step1MathDataStrong Cell T) : RegionCore Cell T :=
  X.core.brightRegion

def interfaceRegion (X : Step1MathDataStrong Cell T) : RegionCore Cell T :=
  X.core.interfaceRegion

def darkRegion (X : Step1MathDataStrong Cell T) : RegionCore Cell T :=
  X.core.darkRegion

theorem core_eq_source (X : Step1MathDataStrong Cell T) :
    X.core = X.source := by
  rfl

theorem exportData_eq_source_exportData (X : Step1MathDataStrong Cell T) :
    X.exportData = X.source.exportData := by
  rfl

theorem carrier_eq_source_carrier (X : Step1MathDataStrong Cell T) :
    X.carrier = X.source.carrier := by
  rfl

theorem regularization_eq_source_regularization (X : Step1MathDataStrong Cell T) :
    X.regularization = X.source.regularization := by
  rfl

theorem schur_eq_source_schur (X : Step1MathDataStrong Cell T) :
    X.schur = X.source.schur := by
  rfl

theorem regionNet_eq_source_regionNet (X : Step1MathDataStrong Cell T) :
    X.regionNet = X.source.regionNet := by
  rfl

theorem split_eq_source_split (X : Step1MathDataStrong Cell T) :
    X.split = X.source.split := by
  rfl

theorem approximant_eq_source_approximant (X : Step1MathDataStrong Cell T) :
    X.approximant = X.source.approximant := by
  rfl

theorem dirichlet_eq_source_dirichlet (X : Step1MathDataStrong Cell T) :
    X.dirichlet = X.source.dirichlet := by
  rfl

theorem binary_eq_source_binary (X : Step1MathDataStrong Cell T) :
    X.binary = X.source.binary := by
  rfl

theorem closureStabilizedBinary_eq_source_closureStabilizedBinary
    (X : Step1MathDataStrong Cell T) :
    X.closureStabilizedBinary = X.source.closureStabilizedBinary := by
  rfl

theorem couplingStabilizedBinary_eq_source_couplingStabilizedBinary
    (X : Step1MathDataStrong Cell T) :
    X.couplingStabilizedBinary = X.source.couplingStabilizedBinary := by
  rfl

theorem generalized_eq_source_generalized (X : Step1MathDataStrong Cell T) :
    X.generalized = X.source.generalized := by
  rfl

theorem selectedLevel_eq_source_selectedLevel (X : Step1MathDataStrong Cell T) :
    X.selectedLevel = X.source.selectedLevel := by
  rfl

theorem candidateLevels_eq_source_candidateLevels (X : Step1MathDataStrong Cell T) :
    X.candidateLevels = X.source.candidateLevels := by
  rfl

theorem irLevels_eq_source_irLevels (X : Step1MathDataStrong Cell T) :
    X.irLevels = X.source.irLevels := by
  rfl

theorem uvLevels_eq_source_uvLevels (X : Step1MathDataStrong Cell T) :
    X.uvLevels = X.source.uvLevels := by
  rfl

theorem epsilon_eq_source_epsilon (X : Step1MathDataStrong Cell T) :
    X.epsilon = X.source.epsilon := by
  rfl

theorem regularizationShift_eq_source_regularizationShift (X : Step1MathDataStrong Cell T) :
    X.regularizationShift = X.source.regularizationShift := by
  rfl

theorem regularization_split_eq_split (X : Step1MathDataStrong Cell T) :
    X.regularization.split = X.split := by
  exact X.source.regularization_split_eq_split

theorem schur_split_eq_split (X : Step1MathDataStrong Cell T) :
    X.schur.split = X.split := by
  exact X.source.schur_split_eq_split

theorem selectedLevelAdmissible (X : Step1MathDataStrong Cell T) :
    X.selectedLevel ∈ X.candidateLevels := by
  exact X.source.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (X : Step1MathDataStrong Cell T) :
    X.selectedLevel ≤ X.cutoff := by
  exact X.source.selectedLevel_le_cutoff

theorem epsilon_pos (X : Step1MathDataStrong Cell T) :
    0 < X.epsilon := by
  exact X.source.epsilon_pos

theorem regularizationShift_pos (X : Step1MathDataStrong Cell T) :
    0 < X.regularizationShift := by
  exact X.source.regularizationShift_pos

theorem regularizationShift_ge_epsilon (X : Step1MathDataStrong Cell T) :
    X.epsilon ≤ X.regularizationShift := by
  exact X.source.regularizationShift_ge_epsilon

theorem hasUVTail_iff_nonempty (X : Step1MathDataStrong Cell T) :
    X.hasUVTail ↔ X.uvLevels.Nonempty := by
  exact X.source.hasUVTail_iff_nonempty

theorem noOuterEnvironment_iff_split (X : Step1MathDataStrong Cell T) :
    X.noOuterEnvironment ↔ X.split.noOuterEnvironment := by
  exact X.source.noOuterEnvironment_iff_split

theorem hasOuterEnvironment_iff_split (X : Step1MathDataStrong Cell T) :
    X.hasOuterEnvironment ↔ X.split.hasOuterEnvironment := by
  exact X.source.hasOuterEnvironment_iff_split

theorem stable_eq_truncate (X : Step1MathDataStrong Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.source.stable_eq_truncate

theorem stableCarrier_eq_ideal_of_le
    (X : Step1MathDataStrong Cell T) {L : Nat} (hL : L ≤ X.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  exact X.source.stableCarrier_eq_ideal_of_le hL

theorem stableCarrier_eq_empty_of_gt
    (X : Step1MathDataStrong Cell T) {L : Nat} (hL : X.cutoff < L) :
    X.stableCarrier L = ∅ := by
  exact X.source.stableCarrier_eq_empty_of_gt hL

end Step1MathDataStrong

end CNNA.PillarA.Handoff
