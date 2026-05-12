import CNNA.PillarA.Closure.ParameterClosure

set_option autoImplicit false

namespace CNNA.PillarA.Closure

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors

universe u

structure RegularizationClosureStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : ParameterClosureStrong Cell T

abbrev RegularizationClosureStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  RegularizationClosureStrong (Cell := Cell) T

namespace RegularizationClosureStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (R S : RegularizationClosureStrong Cell T)
    (hsource : R.source = S.source) :
    R = S := by
  cases R with
  | mk sourceR =>
    cases S with
    | mk sourceS =>
      cases hsource
      rfl

def cast (h : T = U) (R : RegularizationClosureStrong Cell T) :
    RegularizationClosureStrong Cell U := by
  cases h
  exact R

theorem cast_rfl (R : RegularizationClosureStrong Cell T) :
    cast (Cell := Cell) rfl R = R := by
  rfl

def ofParameterClosure (P : ParameterClosureStrong Cell T) :
    RegularizationClosureStrong Cell T where
  source := P

theorem ofParameterClosure_source (P : ParameterClosureStrong Cell T) :
    (ofParameterClosure P).source = P := by
  rfl

abbrev boundaryVertex (R : RegularizationClosureStrong Cell T) :=
  R.source.boundaryVertex

abbrev boundaryPotential (R : RegularizationClosureStrong Cell T) :=
  R.boundaryVertex → ℝ

def stabilizedSource (R : RegularizationClosureStrong Cell T) : DtNStabilizedStrong Cell T :=
  R.source.source

def selector (R : RegularizationClosureStrong Cell T) : BranchingSelectorStrong Cell T :=
  R.source.selector

def branching (R : RegularizationClosureStrong Cell T) : SelectedBranchingStrong Cell T :=
  R.source.branching

def uv (R : RegularizationClosureStrong Cell T) : UVSpectralSelectorStrong Cell T :=
  R.source.uv

def split (R : RegularizationClosureStrong Cell T) : SectorSplitStrong Cell T :=
  R.source.split

def witness (R : RegularizationClosureStrong Cell T) : BranchingWitnessStrong Cell T :=
  R.source.witness

def cutoff (_ : RegularizationClosureStrong Cell T) : Nat :=
  T.cutoff

def selectedLevel (R : RegularizationClosureStrong Cell T) : Nat :=
  R.source.selectedLevel

def candidateLevels (R : RegularizationClosureStrong Cell T) : Finset Nat :=
  R.source.candidateLevels

def irLevels (R : RegularizationClosureStrong Cell T) : Finset Nat :=
  R.source.irLevels

def uvLevels (R : RegularizationClosureStrong Cell T) : Finset Nat :=
  R.source.uvLevels

def hasUVTail (R : RegularizationClosureStrong Cell T) : Prop :=
  R.source.hasUVTail

def regularizationPolicy (R : RegularizationClosureStrong Cell T) : RegularizationPolicy :=
  R.source.regularizationPolicy

def epsilon (R : RegularizationClosureStrong Cell T) : ℝ :=
  R.source.epsilon

theorem epsilon_pos (R : RegularizationClosureStrong Cell T) :
    0 < R.epsilon := by
  exact R.source.epsilon_pos

def comparisonOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ExecComplex :=
  R.source.comparisonOperator

def comparisonFrobeniusSq (R : RegularizationClosureStrong Cell T) : ℚ :=
  R.source.comparisonFrobeniusSq

def regularizationShiftQ (R : RegularizationClosureStrong Cell T) : ℚ :=
  R.source.regularizationShiftQ

def regularizationShift (R : RegularizationClosureStrong Cell T) : ℝ :=
  R.source.regularizationShift

theorem regularizationShift_pos (R : RegularizationClosureStrong Cell T) :
    0 < R.regularizationShift := by
  exact R.source.regularizationShift_pos

theorem regularizationShift_nonneg (R : RegularizationClosureStrong Cell T) :
    0 ≤ R.regularizationShift := by
  exact R.source.regularizationShift_nonneg

theorem regularizationShift_ge_epsilon (R : RegularizationClosureStrong Cell T) :
    R.epsilon ≤ R.regularizationShift := by
  exact R.source.regularizationShift_ge_epsilon

theorem epsilon_eq_source_epsilon (R : RegularizationClosureStrong Cell T) :
    R.epsilon = R.source.epsilon := by
  rfl

theorem regularizationShift_eq_source_regularizationShift
    (R : RegularizationClosureStrong Cell T) :
    R.regularizationShift = R.source.regularizationShift := by
  rfl

def rawBoundaryOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.source.rawBoundaryOperator

def symmetrizedBoundaryOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.source.symmetrizedBoundaryOperator

abbrev symmetrizedOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.symmetrizedBoundaryOperator

def stabilizedOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.source.stabilizedOperator

def stabilizedSymmetricOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.source.stabilizedSymmetricOperator

def regularizedOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.stabilizedOperator

def regularizedSymmetricOperator (R : RegularizationClosureStrong Cell T) :
    Matrix R.boundaryVertex R.boundaryVertex ℝ :=
  R.stabilizedSymmetricOperator

def regularizedFlux (R : RegularizationClosureStrong Cell T)
    (φ : R.boundaryPotential) :
    R.boundaryPotential :=
  R.source.stabilizedFlux φ

def selectedSlice (R : RegularizationClosureStrong Cell T) : LayerSlice Cell :=
  R.source.selectedSlice

def selectedCarrier (R : RegularizationClosureStrong Cell T) : Finset (Cell R.selectedLevel) :=
  R.source.selectedCarrier

def selectedBoundaryCarrier (R : RegularizationClosureStrong Cell T) : Finset (Cell R.selectedLevel) :=
  R.source.selectedBoundaryCarrier

def selectedBrightCarrier (R : RegularizationClosureStrong Cell T) : Finset (Cell R.selectedLevel) :=
  R.source.selectedBrightCarrier

def selectedDarkCarrier (R : RegularizationClosureStrong Cell T) : Finset (Cell R.selectedLevel) :=
  R.source.selectedDarkCarrier

def selectedSectorCount (R : RegularizationClosureStrong Cell T) : Nat :=
  R.source.selectedSectorCount

def brightActive (R : RegularizationClosureStrong Cell T) : Prop :=
  R.source.brightActive

def interfaceActive (R : RegularizationClosureStrong Cell T) : Prop :=
  R.source.interfaceActive

def darkActive (R : RegularizationClosureStrong Cell T) : Prop :=
  R.source.darkActive

def noOuterEnvironment (R : RegularizationClosureStrong Cell T) : Prop :=
  R.source.noOuterEnvironment

def hasOuterEnvironment (R : RegularizationClosureStrong Cell T) : Prop :=
  R.source.hasOuterEnvironment

theorem selector_eq_source_selector (R : RegularizationClosureStrong Cell T) :
    R.selector = R.source.selector := by
  rfl

theorem stabilizedSource_eq_source_source (R : RegularizationClosureStrong Cell T) :
    R.stabilizedSource = R.source.source := by
  rfl

theorem regularizedOperator_eq_stabilizedOperator (R : RegularizationClosureStrong Cell T) :
    R.regularizedOperator = R.stabilizedOperator := by
  rfl

theorem regularizedSymmetricOperator_eq_stabilizedSymmetricOperator
    (R : RegularizationClosureStrong Cell T) :
    R.regularizedSymmetricOperator = R.stabilizedSymmetricOperator := by
  rfl

theorem uv_source_eq_branching (R : RegularizationClosureStrong Cell T) :
    R.uv.source = R.branching := by
  exact R.source.uv_source_eq_branching

theorem selectedLevel_eq_branching (R : RegularizationClosureStrong Cell T) :
    R.selectedLevel = R.branching.selectedLevel := by
  exact R.source.selectedLevel_eq_branching

theorem uv_selectedLevel_eq (R : RegularizationClosureStrong Cell T) :
    R.uv.selectedLevel = R.selectedLevel := by
  exact R.source.uv_selectedLevel_eq

theorem selectedLevelAdmissible (R : RegularizationClosureStrong Cell T) :
    R.selectedLevel ∈ R.candidateLevels := by
  exact R.source.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (R : RegularizationClosureStrong Cell T) :
    R.selectedLevel ≤ T.cutoff := by
  exact R.source.selectedLevel_le_cutoff

theorem mem_irLevels_iff (R : RegularizationClosureStrong Cell T) (L : Nat) :
    L ∈ R.irLevels ↔ L ≤ R.selectedLevel := by
  exact R.source.mem_irLevels_iff L

theorem mem_uvLevels_iff (R : RegularizationClosureStrong Cell T) (L : Nat) :
    L ∈ R.uvLevels ↔ R.selectedLevel < L ∧ L ≤ T.cutoff := by
  exact R.source.mem_uvLevels_iff L

theorem hasUVTail_iff_nonempty (R : RegularizationClosureStrong Cell T) :
    R.hasUVTail ↔ R.uvLevels.Nonempty := by
  exact R.source.hasUVTail_iff_nonempty

theorem noUVTail_iff (R : RegularizationClosureStrong Cell T) :
    ¬ R.hasUVTail ↔ R.uvLevels = ∅ := by
  exact R.source.noUVTail_iff

theorem ir_uv_disjoint (R : RegularizationClosureStrong Cell T) :
    Disjoint R.irLevels R.uvLevels := by
  exact R.source.ir_uv_disjoint

theorem ir_uv_cover (R : RegularizationClosureStrong Cell T) :
    R.irLevels ∪ R.uvLevels = Finset.range (T.cutoff + 1) := by
  exact R.source.ir_uv_cover

theorem selectedCarrier_subset (R : RegularizationClosureStrong Cell T) :
    R.selectedCarrier ⊆ T.carrier R.selectedLevel := by
  exact R.source.selectedCarrier_subset

theorem selectedBoundaryCarrier_subset (R : RegularizationClosureStrong Cell T) :
    R.selectedBoundaryCarrier ⊆ T.carrier R.selectedLevel := by
  exact R.source.selectedBoundaryCarrier_subset

theorem selectedSectorCount_ge_two (R : RegularizationClosureStrong Cell T) :
    2 ≤ R.selectedSectorCount := by
  exact R.source.selectedSectorCount_ge_two

theorem selectedSectorCover (R : RegularizationClosureStrong Cell T) :
    R.selectedBrightCarrier ∪ R.selectedBoundaryCarrier ∪ R.selectedDarkCarrier =
      T.carrier R.selectedLevel := by
  exact R.source.selectedSectorCover

theorem noOuterEnvironment_iff (R : RegularizationClosureStrong Cell T) :
    R.noOuterEnvironment ↔ R.split.noOuterEnvironment := by
  exact R.source.noOuterEnvironment_iff

theorem hasOuterEnvironment_iff (R : RegularizationClosureStrong Cell T) :
    R.hasOuterEnvironment ↔ R.split.hasOuterEnvironment := by
  exact R.source.hasOuterEnvironment_iff

theorem symmetrizedBoundaryOperator_transpose (R : RegularizationClosureStrong Cell T) :
    Matrix.transpose R.symmetrizedBoundaryOperator = R.symmetrizedBoundaryOperator := by
  exact R.source.symmetrizedBoundaryOperator_transpose

theorem symmetrizedOperator_transpose (R : RegularizationClosureStrong Cell T) :
    Matrix.transpose R.symmetrizedOperator = R.symmetrizedOperator := by
  exact R.source.symmetrizedOperator_transpose

theorem regularizationShift_eq_policy_canonicalShift (R : RegularizationClosureStrong Cell T) :
    R.regularizationShift = R.regularizationPolicy.canonicalShift R.comparisonOperator := by
  exact R.source.regularizationShift_eq_policy_canonicalShift

theorem stabilizedOperator_eq_raw_plus_shift (R : RegularizationClosureStrong Cell T) :
    R.stabilizedOperator =
      R.rawBoundaryOperator +
        R.regularizationShift • (1 : Matrix R.boundaryVertex R.boundaryVertex ℝ) := by
  exact R.source.stabilizedOperator_eq_raw_plus_shift

theorem regularizedOperator_eq_raw_plus_shift (R : RegularizationClosureStrong Cell T) :
    R.regularizedOperator =
      R.rawBoundaryOperator +
        R.regularizationShift • (1 : Matrix R.boundaryVertex R.boundaryVertex ℝ) := by
  exact R.stabilizedOperator_eq_raw_plus_shift

theorem stabilizedSymmetricOperator_transpose (R : RegularizationClosureStrong Cell T) :
    Matrix.transpose R.stabilizedSymmetricOperator = R.stabilizedSymmetricOperator := by
  exact R.source.stabilizedSymmetricOperator_transpose

theorem regularizedSymmetricOperator_transpose (R : RegularizationClosureStrong Cell T) :
    Matrix.transpose R.regularizedSymmetricOperator = R.regularizedSymmetricOperator := by
  exact R.stabilizedSymmetricOperator_transpose

theorem regularizedFlux_eq_mulVec
    (R : RegularizationClosureStrong Cell T) (φ : R.boundaryPotential) :
    R.regularizedFlux φ = (R.regularizedOperator).mulVec φ := by
  exact R.source.stabilizedFlux_eq_mulVec φ

end RegularizationClosureStrong

namespace StrengtheningS6

open CNNA.PillarA.Finite.StrengtheningS4

def referenceFullRegularizationClosure (b : Nat) (p : ConcretePolicyOf)
    (selector : BranchingSelectorStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p))
    (wp : WeightPolicy := CNNA.PillarA.Finite.StrengtheningS5.referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := CNNA.PillarA.DtN.StrengtheningS6.referenceDefaultRegularizationPolicy)
    [CNNA.PillarA.DtN.StrengtheningS5.ReferenceInteriorEliminationData b p wp]
    : RegularizationClosureStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  RegularizationClosureStrong.ofParameterClosure
    (referenceFullParameterClosure b p selector wp rp)

def variationFullRegularizationClosure (β : Nat → Nat) (p : ConcretePolicyOf)
    (selector : BranchingSelectorStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p))
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [CNNA.PillarA.DtN.StrengtheningS5.VariationInteriorEliminationData β p wp]
    : RegularizationClosureStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  RegularizationClosureStrong.ofParameterClosure
    (variationFullParameterClosure β p selector wp rp)

end StrengtheningS6

end CNNA.PillarA.Closure
