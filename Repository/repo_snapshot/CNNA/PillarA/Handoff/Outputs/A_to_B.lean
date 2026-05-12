import CNNA.PillarA.Handoff.Core.Step1MathData

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

structure ABHandoffStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : Step1MathDataStrong Cell T
  payload : SectorExportStrong Cell T
  payload_eq_source_exportData : payload = source.exportData

abbrev ABHandoffStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ABHandoffStrong (Cell := Cell) T

namespace ABHandoffStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : ABHandoffStrong Cell T)
    (hsource : X.source = Y.source)
    (hpayload : X.payload = Y.payload) :
    X = Y := by
  cases X with
  | mk sourceX payloadX hpayloadX =>
    cases Y with
    | mk sourceY payloadY hpayloadY =>
      cases hsource
      cases hpayload
      have hproof : hpayloadX = hpayloadY := Subsingleton.elim _ _
      cases hproof
      rfl

def cast (h : T = U) (X : ABHandoffStrong Cell T) :
    ABHandoffStrong Cell U := by
  cases h
  exact X

theorem cast_rfl (X : ABHandoffStrong Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofStep1MathData (X : Step1MathDataStrong Cell T) :
    ABHandoffStrong Cell T where
  source := X
  payload := X.exportData
  payload_eq_source_exportData := rfl

theorem ofStep1MathData_source (X : Step1MathDataStrong Cell T) :
    (ofStep1MathData X).source = X := by
  rfl

theorem ofStep1MathData_payload (X : Step1MathDataStrong Cell T) :
    (ofStep1MathData X).payload = X.exportData := by
  rfl

def mathData (X : ABHandoffStrong Cell T) : Step1MathDataStrong Cell T :=
  X.source

def core (X : ABHandoffStrong Cell T) : Step1StrongCore Cell T :=
  X.mathData.core

def exportData (X : ABHandoffStrong Cell T) : SectorExportStrong Cell T :=
  X.payload

def aToBInput (X : ABHandoffStrong Cell T) : SectorExportStrong Cell T :=
  X.exportData

def carrier (X : ABHandoffStrong Cell T) : InfiniteCarrierStrong Cell T :=
  X.exportData.carrier

def regularization (X : ABHandoffStrong Cell T) : RegularizationClosureStrong Cell T :=
  X.exportData.regularization

def schur (X : ABHandoffStrong Cell T) : MultiSchurStrong Cell T :=
  X.exportData.schur

def regionNet (X : ABHandoffStrong Cell T) : RegionNetStrong Cell T :=
  X.exportData.regionNet

def split (X : ABHandoffStrong Cell T) : SectorSplitStrong Cell T :=
  X.exportData.split

def approximant (X : ABHandoffStrong Cell T) : ApproximantStrong Cell T :=
  X.exportData.approximant

def ideal (X : ABHandoffStrong Cell T) : DirectedFamily (Cell := Cell) :=
  X.mathData.ideal

def cutoff (X : ABHandoffStrong Cell T) : Nat :=
  X.mathData.cutoff

def dirichlet (X : ABHandoffStrong Cell T) : DirichletLaplacianStrong Cell T :=
  X.mathData.dirichlet

def binary (X : ABHandoffStrong Cell T) : DtNStrong Cell T :=
  X.mathData.binary

def closureStabilizedBinary (X : ABHandoffStrong Cell T) : DtNStabilizedStrong Cell T :=
  X.mathData.closureStabilizedBinary

def generalized (X : ABHandoffStrong Cell T) : GeneralizedDtNStrong Cell T :=
  X.mathData.generalized

def couplingStabilizedBinary (X : ABHandoffStrong Cell T) : DtNStabilizedStrong Cell T :=
  X.mathData.couplingStabilizedBinary

def selector (X : ABHandoffStrong Cell T) : BranchingSelectorStrong Cell T :=
  X.mathData.selector

def witness (X : ABHandoffStrong Cell T) : BranchingWitnessStrong Cell T :=
  X.mathData.witness

def branching (X : ABHandoffStrong Cell T) : SelectedBranchingStrong Cell T :=
  X.mathData.branching

def uv (X : ABHandoffStrong Cell T) : UVSpectralSelectorStrong Cell T :=
  X.mathData.uv

def selectedLevel (X : ABHandoffStrong Cell T) : Nat :=
  X.mathData.selectedLevel

def candidateLevels (X : ABHandoffStrong Cell T) : Finset Nat :=
  X.mathData.candidateLevels

def irLevels (X : ABHandoffStrong Cell T) : Finset Nat :=
  X.mathData.irLevels

def uvLevels (X : ABHandoffStrong Cell T) : Finset Nat :=
  X.mathData.uvLevels

def hasUVTail (X : ABHandoffStrong Cell T) : Prop :=
  X.mathData.hasUVTail

def epsilon (X : ABHandoffStrong Cell T) : ℝ :=
  X.mathData.epsilon

def regularizationShift (X : ABHandoffStrong Cell T) : ℝ :=
  X.mathData.regularizationShift

def noOuterEnvironment (X : ABHandoffStrong Cell T) : Prop :=
  X.mathData.noOuterEnvironment

def hasOuterEnvironment (X : ABHandoffStrong Cell T) : Prop :=
  X.mathData.hasOuterEnvironment

def stableCarrier (X : ABHandoffStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.mathData.stableCarrier L

def idealCarrier (X : ABHandoffStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.mathData.idealCarrier L

theorem mathData_eq_source (X : ABHandoffStrong Cell T) :
    X.mathData = X.source := by
  rfl

theorem exportData_eq_payload (X : ABHandoffStrong Cell T) :
    X.exportData = X.payload := by
  rfl

theorem aToBInput_eq_exportData (X : ABHandoffStrong Cell T) :
    X.aToBInput = X.exportData := by
  rfl

theorem payload_eq_math_exportData (X : ABHandoffStrong Cell T) :
    X.payload = X.source.exportData := by
  exact X.payload_eq_source_exportData

theorem closureStabilizedBinary_eq_source_closureStabilizedBinary
    (X : ABHandoffStrong Cell T) :
    X.closureStabilizedBinary = X.source.closureStabilizedBinary := by
  rfl

theorem couplingStabilizedBinary_eq_source_couplingStabilizedBinary
    (X : ABHandoffStrong Cell T) :
    X.couplingStabilizedBinary = X.source.couplingStabilizedBinary := by
  rfl


theorem carrier_eq_source_carrier (X : ABHandoffStrong Cell T) :
    X.carrier = X.source.carrier := by
  change X.payload.carrier = X.source.carrier
  rw [X.payload_eq_math_exportData]
  rfl

theorem regularization_eq_source_regularization (X : ABHandoffStrong Cell T) :
    X.regularization = X.source.regularization := by
  change X.payload.regularization = X.source.regularization
  rw [X.payload_eq_math_exportData]
  rfl

theorem schur_eq_source_schur (X : ABHandoffStrong Cell T) :
    X.schur = X.source.schur := by
  change X.payload.schur = X.source.schur
  rw [X.payload_eq_math_exportData]
  rfl

theorem regionNet_eq_source_regionNet (X : ABHandoffStrong Cell T) :
    X.regionNet = X.source.regionNet := by
  change X.payload.regionNet = X.source.regionNet
  rw [X.payload_eq_math_exportData]
  rfl

theorem split_eq_source_split (X : ABHandoffStrong Cell T) :
    X.split = X.source.split := by
  change X.payload.split = X.source.split
  rw [X.payload_eq_math_exportData]
  rfl

theorem approximant_eq_source_approximant (X : ABHandoffStrong Cell T) :
    X.approximant = X.source.approximant := by
  change X.payload.approximant = X.source.approximant
  rw [X.payload_eq_math_exportData]
  rfl

theorem selectedLevel_eq_source_selectedLevel (X : ABHandoffStrong Cell T) :
    X.selectedLevel = X.source.selectedLevel := by
  rfl

theorem candidateLevels_eq_source_candidateLevels (X : ABHandoffStrong Cell T) :
    X.candidateLevels = X.source.candidateLevels := by
  rfl

theorem irLevels_eq_source_irLevels (X : ABHandoffStrong Cell T) :
    X.irLevels = X.source.irLevels := by
  rfl

theorem uvLevels_eq_source_uvLevels (X : ABHandoffStrong Cell T) :
    X.uvLevels = X.source.uvLevels := by
  rfl

theorem epsilon_eq_source_epsilon (X : ABHandoffStrong Cell T) :
    X.epsilon = X.source.epsilon := by
  rfl

theorem regularizationShift_eq_source_regularizationShift (X : ABHandoffStrong Cell T) :
    X.regularizationShift = X.source.regularizationShift := by
  rfl

theorem selectedLevelAdmissible (X : ABHandoffStrong Cell T) :
    X.selectedLevel ∈ X.candidateLevels := by
  exact X.source.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (X : ABHandoffStrong Cell T) :
    X.selectedLevel ≤ X.cutoff := by
  exact X.source.selectedLevel_le_cutoff

theorem epsilon_pos (X : ABHandoffStrong Cell T) :
    0 < X.epsilon := by
  exact X.source.epsilon_pos

theorem regularizationShift_pos (X : ABHandoffStrong Cell T) :
    0 < X.regularizationShift := by
  exact X.source.regularizationShift_pos

theorem regularizationShift_ge_epsilon (X : ABHandoffStrong Cell T) :
    X.epsilon ≤ X.regularizationShift := by
  exact X.source.regularizationShift_ge_epsilon

theorem hasUVTail_iff_nonempty (X : ABHandoffStrong Cell T) :
    X.hasUVTail ↔ X.uvLevels.Nonempty := by
  exact X.source.hasUVTail_iff_nonempty

theorem noOuterEnvironment_iff_split (X : ABHandoffStrong Cell T) :
    X.noOuterEnvironment ↔ X.split.noOuterEnvironment := by
  change X.source.noOuterEnvironment ↔ X.payload.split.noOuterEnvironment
  rw [X.payload_eq_math_exportData]
  exact X.source.noOuterEnvironment_iff_split

theorem hasOuterEnvironment_iff_split (X : ABHandoffStrong Cell T) :
    X.hasOuterEnvironment ↔ X.split.hasOuterEnvironment := by
  change X.source.hasOuterEnvironment ↔ X.payload.split.hasOuterEnvironment
  rw [X.payload_eq_math_exportData]
  exact X.source.hasOuterEnvironment_iff_split

theorem stable_eq_truncate (X : ABHandoffStrong Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.source.stable_eq_truncate

theorem stableCarrier_eq_ideal_of_le
    (X : ABHandoffStrong Cell T) {L : Nat} (hL : L ≤ X.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  exact X.source.stableCarrier_eq_ideal_of_le hL

theorem stableCarrier_eq_empty_of_gt
    (X : ABHandoffStrong Cell T) {L : Nat} (hL : X.cutoff < L) :
    X.stableCarrier L = ∅ := by
  exact X.source.stableCarrier_eq_empty_of_gt hL

end ABHandoffStrong

end CNNA.PillarA.Handoff
