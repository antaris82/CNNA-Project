import CNNA.PillarA.Handoff.Outputs.A_to_B

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

structure PillarAStep1Closed (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : ABHandoffStrong Cell T

abbrev PillarAStep1ClosedOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  PillarAStep1Closed (Cell := Cell) T

namespace PillarAStep1Closed

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : PillarAStep1Closed Cell T)
    (hsource : X.source = Y.source) :
    X = Y := by
  cases X with
  | mk sourceX =>
    cases Y with
    | mk sourceY =>
      cases hsource
      rfl

def cast (h : T = U) (X : PillarAStep1Closed Cell T) :
    PillarAStep1Closed Cell U := by
  cases h
  exact X

theorem cast_rfl (X : PillarAStep1Closed Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofABHandoff (X : ABHandoffStrong Cell T) :
    PillarAStep1Closed Cell T where
  source := X

theorem ofABHandoff_source (X : ABHandoffStrong Cell T) :
    (ofABHandoff X).source = X := by
  rfl

def handoff (X : PillarAStep1Closed Cell T) : ABHandoffStrong Cell T :=
  X.source

def mathData (X : PillarAStep1Closed Cell T) : Step1MathDataStrong Cell T :=
  X.handoff.mathData

def core (X : PillarAStep1Closed Cell T) : Step1StrongCore Cell T :=
  X.handoff.core

def exportData (X : PillarAStep1Closed Cell T) : SectorExportStrong Cell T :=
  X.handoff.exportData

def aToBInput (X : PillarAStep1Closed Cell T) : SectorExportStrong Cell T :=
  X.handoff.aToBInput

def carrier (X : PillarAStep1Closed Cell T) : InfiniteCarrierStrong Cell T :=
  X.handoff.carrier

def regularization (X : PillarAStep1Closed Cell T) : RegularizationClosureStrong Cell T :=
  X.handoff.regularization

def schur (X : PillarAStep1Closed Cell T) : MultiSchurStrong Cell T :=
  X.handoff.schur

def regionNet (X : PillarAStep1Closed Cell T) : RegionNetStrong Cell T :=
  X.handoff.regionNet

def split (X : PillarAStep1Closed Cell T) : SectorSplitStrong Cell T :=
  X.handoff.split

def approximant (X : PillarAStep1Closed Cell T) : ApproximantStrong Cell T :=
  X.handoff.approximant

def ideal (X : PillarAStep1Closed Cell T) : DirectedFamily (Cell := Cell) :=
  X.handoff.ideal

def cutoff (X : PillarAStep1Closed Cell T) : Nat :=
  X.handoff.cutoff

def dirichlet (X : PillarAStep1Closed Cell T) : DirichletLaplacianStrong Cell T :=
  X.handoff.dirichlet

def binary (X : PillarAStep1Closed Cell T) : DtNStrong Cell T :=
  X.handoff.binary

def closureStabilizedBinary (X : PillarAStep1Closed Cell T) : DtNStabilizedStrong Cell T :=
  X.handoff.closureStabilizedBinary

def generalized (X : PillarAStep1Closed Cell T) : GeneralizedDtNStrong Cell T :=
  X.handoff.generalized

def couplingStabilizedBinary (X : PillarAStep1Closed Cell T) : DtNStabilizedStrong Cell T :=
  X.handoff.couplingStabilizedBinary

def selector (X : PillarAStep1Closed Cell T) : BranchingSelectorStrong Cell T :=
  X.handoff.selector

def witness (X : PillarAStep1Closed Cell T) : BranchingWitnessStrong Cell T :=
  X.handoff.witness

def branching (X : PillarAStep1Closed Cell T) : SelectedBranchingStrong Cell T :=
  X.handoff.branching

def uv (X : PillarAStep1Closed Cell T) : UVSpectralSelectorStrong Cell T :=
  X.handoff.uv

def selectedLevel (X : PillarAStep1Closed Cell T) : Nat :=
  X.handoff.selectedLevel

def candidateLevels (X : PillarAStep1Closed Cell T) : Finset Nat :=
  X.handoff.candidateLevels

def irLevels (X : PillarAStep1Closed Cell T) : Finset Nat :=
  X.handoff.irLevels

def uvLevels (X : PillarAStep1Closed Cell T) : Finset Nat :=
  X.handoff.uvLevels

def hasUVTail (X : PillarAStep1Closed Cell T) : Prop :=
  X.handoff.hasUVTail

def epsilon (X : PillarAStep1Closed Cell T) : ℝ :=
  X.handoff.epsilon

def regularizationShift (X : PillarAStep1Closed Cell T) : ℝ :=
  X.handoff.regularizationShift

def noOuterEnvironment (X : PillarAStep1Closed Cell T) : Prop :=
  X.handoff.noOuterEnvironment

def hasOuterEnvironment (X : PillarAStep1Closed Cell T) : Prop :=
  X.handoff.hasOuterEnvironment

def stableCarrier (X : PillarAStep1Closed Cell T) (L : Nat) : Finset (Cell L) :=
  X.handoff.stableCarrier L

def idealCarrier (X : PillarAStep1Closed Cell T) (L : Nat) : Finset (Cell L) :=
  X.handoff.idealCarrier L

theorem handoff_eq_source (X : PillarAStep1Closed Cell T) :
    X.handoff = X.source := by
  rfl

theorem mathData_eq_handoff_mathData (X : PillarAStep1Closed Cell T) :
    X.mathData = X.handoff.mathData := by
  rfl

theorem core_eq_handoff_core (X : PillarAStep1Closed Cell T) :
    X.core = X.handoff.core := by
  rfl

theorem exportData_eq_handoff_exportData (X : PillarAStep1Closed Cell T) :
    X.exportData = X.handoff.exportData := by
  rfl

theorem closureStabilizedBinary_eq_handoff_closureStabilizedBinary
    (X : PillarAStep1Closed Cell T) :
    X.closureStabilizedBinary = X.handoff.closureStabilizedBinary := by
  rfl

theorem couplingStabilizedBinary_eq_handoff_couplingStabilizedBinary
    (X : PillarAStep1Closed Cell T) :
    X.couplingStabilizedBinary = X.handoff.couplingStabilizedBinary := by
  rfl


theorem aToBInput_eq_handoff_aToBInput (X : PillarAStep1Closed Cell T) :
    X.aToBInput = X.handoff.aToBInput := by
  rfl

theorem carrier_eq_handoff_carrier (X : PillarAStep1Closed Cell T) :
    X.carrier = X.handoff.carrier := by
  rfl

theorem split_eq_handoff_split (X : PillarAStep1Closed Cell T) :
    X.split = X.handoff.split := by
  rfl

theorem selectedLevel_eq_handoff_selectedLevel (X : PillarAStep1Closed Cell T) :
    X.selectedLevel = X.handoff.selectedLevel := by
  rfl

theorem epsilon_eq_handoff_epsilon (X : PillarAStep1Closed Cell T) :
    X.epsilon = X.handoff.epsilon := by
  rfl

theorem regularizationShift_eq_handoff_regularizationShift
    (X : PillarAStep1Closed Cell T) :
    X.regularizationShift = X.handoff.regularizationShift := by
  rfl

theorem selectedLevelAdmissible (X : PillarAStep1Closed Cell T) :
    X.selectedLevel ∈ X.candidateLevels := by
  exact X.handoff.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (X : PillarAStep1Closed Cell T) :
    X.selectedLevel ≤ X.cutoff := by
  exact X.handoff.selectedLevel_le_cutoff

theorem epsilon_pos (X : PillarAStep1Closed Cell T) :
    0 < X.epsilon := by
  exact X.handoff.epsilon_pos

theorem regularizationShift_pos (X : PillarAStep1Closed Cell T) :
    0 < X.regularizationShift := by
  exact X.handoff.regularizationShift_pos

theorem regularizationShift_ge_epsilon (X : PillarAStep1Closed Cell T) :
    X.epsilon ≤ X.regularizationShift := by
  exact X.handoff.regularizationShift_ge_epsilon

theorem hasUVTail_iff_nonempty (X : PillarAStep1Closed Cell T) :
    X.hasUVTail ↔ X.uvLevels.Nonempty := by
  exact X.handoff.hasUVTail_iff_nonempty

theorem noOuterEnvironment_iff_split (X : PillarAStep1Closed Cell T) :
    X.noOuterEnvironment ↔ X.split.noOuterEnvironment := by
  exact X.handoff.noOuterEnvironment_iff_split

theorem hasOuterEnvironment_iff_split (X : PillarAStep1Closed Cell T) :
    X.hasOuterEnvironment ↔ X.split.hasOuterEnvironment := by
  exact X.handoff.hasOuterEnvironment_iff_split

theorem stable_eq_truncate (X : PillarAStep1Closed Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.handoff.stable_eq_truncate

theorem stableCarrier_eq_ideal_of_le
    (X : PillarAStep1Closed Cell T) {L : Nat} (hL : L ≤ X.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  exact X.handoff.stableCarrier_eq_ideal_of_le hL

theorem stableCarrier_eq_empty_of_gt
    (X : PillarAStep1Closed Cell T) {L : Nat} (hL : X.cutoff < L) :
    X.stableCarrier L = ∅ := by
  exact X.handoff.stableCarrier_eq_empty_of_gt hL

end PillarAStep1Closed

end CNNA.PillarA.Handoff
