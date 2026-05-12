import CNNA.PillarA.Sectors.BranchingSelector
import CNNA.PillarA.DtN.DtNStabilized

set_option autoImplicit false

namespace CNNA.PillarA.Closure

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors

universe u

structure ParameterClosureStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : DtNStabilizedStrong Cell T
  selector : BranchingSelectorStrong Cell T

abbrev ParameterClosureStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ParameterClosureStrong (Cell := Cell) T

namespace ParameterClosureStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (P Q : ParameterClosureStrong Cell T)
    (hsource : P.source = Q.source)
    (hselector : P.selector = Q.selector) :
    P = Q := by
  cases P with
  | mk sourceP selectorP =>
    cases Q with
    | mk sourceQ selectorQ =>
      cases hsource
      cases hselector
      rfl

def cast (h : T = U) (P : ParameterClosureStrong Cell T) :
    ParameterClosureStrong Cell U := by
  cases h
  exact P

theorem cast_rfl (P : ParameterClosureStrong Cell T) :
    cast (Cell := Cell) rfl P = P := by
  rfl

def ofDtNAndSelector
    (K : DtNStabilizedStrong Cell T)
    (B : BranchingSelectorStrong Cell T) :
    ParameterClosureStrong Cell T where
  source := K
  selector := B

abbrev boundaryVertex (P : ParameterClosureStrong Cell T) :=
  P.source.boundaryVertex

abbrev boundaryPotential (P : ParameterClosureStrong Cell T) :=
  P.boundaryVertex → ℝ

def branching (P : ParameterClosureStrong Cell T) : SelectedBranchingStrong Cell T :=
  P.selector.branching

def uv (P : ParameterClosureStrong Cell T) : UVSpectralSelectorStrong Cell T :=
  P.selector.uv

def split (P : ParameterClosureStrong Cell T) : SectorSplitStrong Cell T :=
  P.selector.split

def witness (P : ParameterClosureStrong Cell T) : BranchingWitnessStrong Cell T :=
  P.selector.witness

def cutoff (_ : ParameterClosureStrong Cell T) : Nat :=
  T.cutoff

def selectedLevel (P : ParameterClosureStrong Cell T) : Nat :=
  P.selector.selectedLevel

def candidateLevels (P : ParameterClosureStrong Cell T) : Finset Nat :=
  P.selector.candidateLevels

def irLevels (P : ParameterClosureStrong Cell T) : Finset Nat :=
  P.selector.irLevels

def uvLevels (P : ParameterClosureStrong Cell T) : Finset Nat :=
  P.selector.uvLevels

def hasUVTail (P : ParameterClosureStrong Cell T) : Prop :=
  P.selector.hasUVTail

def regularizationPolicy (P : ParameterClosureStrong Cell T) : RegularizationPolicy :=
  P.source.regularizationPolicy

def epsilon (P : ParameterClosureStrong Cell T) : ℝ :=
  P.source.epsilon

theorem epsilon_pos (P : ParameterClosureStrong Cell T) :
    0 < P.epsilon := by
  exact P.source.epsilon_pos

def comparisonOperator (P : ParameterClosureStrong Cell T) :
    Matrix P.boundaryVertex P.boundaryVertex ExecComplex :=
  P.source.comparisonOperator

def comparisonFrobeniusSq (P : ParameterClosureStrong Cell T) : ℚ :=
  P.source.comparisonFrobeniusSq

def regularizationShiftQ (P : ParameterClosureStrong Cell T) : ℚ :=
  P.source.regularizationShiftQ

def regularizationShift (P : ParameterClosureStrong Cell T) : ℝ :=
  P.source.regularizationShift

theorem regularizationShift_pos (P : ParameterClosureStrong Cell T) :
    0 < P.regularizationShift := by
  exact P.source.regularizationShift_pos

theorem regularizationShift_nonneg (P : ParameterClosureStrong Cell T) :
    0 ≤ P.regularizationShift := by
  exact P.source.regularizationShift_nonneg

theorem regularizationShift_ge_epsilon (P : ParameterClosureStrong Cell T) :
    P.epsilon ≤ P.regularizationShift := by
  exact P.source.regularizationShift_ge_epsilon

def rawBoundaryOperator (P : ParameterClosureStrong Cell T) :
    Matrix P.boundaryVertex P.boundaryVertex ℝ :=
  P.source.rawBoundaryOperator

def symmetrizedBoundaryOperator (P : ParameterClosureStrong Cell T) :
    Matrix P.boundaryVertex P.boundaryVertex ℝ :=
  P.source.symmetrizedBoundaryOperator

abbrev symmetrizedOperator (P : ParameterClosureStrong Cell T) :
    Matrix P.boundaryVertex P.boundaryVertex ℝ :=
  P.symmetrizedBoundaryOperator

def stabilizedOperator (P : ParameterClosureStrong Cell T) :
    Matrix P.boundaryVertex P.boundaryVertex ℝ :=
  P.source.stabilizedOperator

def stabilizedSymmetricOperator (P : ParameterClosureStrong Cell T) :
    Matrix P.boundaryVertex P.boundaryVertex ℝ :=
  P.source.stabilizedSymmetricOperator

def stabilizedFlux (P : ParameterClosureStrong Cell T)
    (φ : P.boundaryPotential) :
    P.boundaryPotential :=
  P.source.stabilizedFlux φ

def selectedSlice (P : ParameterClosureStrong Cell T) : LayerSlice Cell :=
  P.uv.selectedSlice

def selectedCarrier (P : ParameterClosureStrong Cell T) : Finset (Cell P.selectedLevel) :=
  P.selector.selectedCarrier

def selectedBoundaryCarrier (P : ParameterClosureStrong Cell T) : Finset (Cell P.selectedLevel) :=
  P.selector.selectedBoundaryCarrier

def selectedBrightCarrier (P : ParameterClosureStrong Cell T) : Finset (Cell P.selectedLevel) :=
  P.selector.selectedBrightCarrier

def selectedDarkCarrier (P : ParameterClosureStrong Cell T) : Finset (Cell P.selectedLevel) :=
  P.selector.selectedDarkCarrier

def selectedSectorCount (P : ParameterClosureStrong Cell T) : Nat :=
  P.selector.selectedSectorCount

def brightActive (P : ParameterClosureStrong Cell T) : Prop :=
  P.selector.brightActive

def interfaceActive (P : ParameterClosureStrong Cell T) : Prop :=
  P.selector.interfaceActive

def darkActive (P : ParameterClosureStrong Cell T) : Prop :=
  P.selector.darkActive

def noOuterEnvironment (P : ParameterClosureStrong Cell T) : Prop :=
  P.selector.noOuterEnvironment

def hasOuterEnvironment (P : ParameterClosureStrong Cell T) : Prop :=
  P.selector.hasOuterEnvironment

theorem uv_source_eq_branching (P : ParameterClosureStrong Cell T) :
    P.uv.source = P.branching := by
  exact P.selector.uv_source_eq_branching

theorem selectedLevel_eq_branching (P : ParameterClosureStrong Cell T) :
    P.selectedLevel = P.branching.selectedLevel := by
  exact P.selector.selectedLevel_eq_branching

theorem uv_selectedLevel_eq (P : ParameterClosureStrong Cell T) :
    P.uv.selectedLevel = P.selectedLevel := by
  exact P.selector.uv_selectedLevel_eq

theorem selectedLevelAdmissible (P : ParameterClosureStrong Cell T) :
    P.selectedLevel ∈ P.candidateLevels := by
  exact P.selector.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (P : ParameterClosureStrong Cell T) :
    P.selectedLevel ≤ T.cutoff := by
  exact P.selector.selectedLevel_le_cutoff

theorem mem_irLevels_iff (P : ParameterClosureStrong Cell T) (L : Nat) :
    L ∈ P.irLevels ↔ L ≤ P.selectedLevel := by
  exact P.selector.mem_irLevels_iff L

theorem mem_uvLevels_iff (P : ParameterClosureStrong Cell T) (L : Nat) :
    L ∈ P.uvLevels ↔ P.selectedLevel < L ∧ L ≤ T.cutoff := by
  exact P.selector.mem_uvLevels_iff L

theorem hasUVTail_iff_nonempty (P : ParameterClosureStrong Cell T) :
    P.hasUVTail ↔ P.uvLevels.Nonempty := by
  exact P.selector.hasUVTail_iff_nonempty

theorem noUVTail_iff (P : ParameterClosureStrong Cell T) :
    ¬ P.hasUVTail ↔ P.uvLevels = ∅ := by
  exact P.selector.noUVTail_iff

theorem ir_uv_disjoint (P : ParameterClosureStrong Cell T) :
    Disjoint P.irLevels P.uvLevels := by
  exact P.selector.ir_uv_disjoint

theorem ir_uv_cover (P : ParameterClosureStrong Cell T) :
    P.irLevels ∪ P.uvLevels = Finset.range (T.cutoff + 1) := by
  exact P.selector.ir_uv_cover

theorem selectedCarrier_subset (P : ParameterClosureStrong Cell T) :
    P.selectedCarrier ⊆ T.carrier P.selectedLevel := by
  exact P.selector.selectedCarrier_subset

theorem selectedBoundaryCarrier_subset (P : ParameterClosureStrong Cell T) :
    P.selectedBoundaryCarrier ⊆ T.carrier P.selectedLevel := by
  exact P.selector.selectedBoundaryCarrier_subset

theorem selectedSectorCount_ge_two (P : ParameterClosureStrong Cell T) :
    2 ≤ P.selectedSectorCount := by
  exact P.selector.selectedSectorCount_ge_two

theorem selectedSectorCover (P : ParameterClosureStrong Cell T) :
    P.selectedBrightCarrier ∪ P.selectedBoundaryCarrier ∪ P.selectedDarkCarrier =
      T.carrier P.selectedLevel := by
  exact P.selector.selectedSectorCover

theorem noOuterEnvironment_iff (P : ParameterClosureStrong Cell T) :
    P.noOuterEnvironment ↔ P.split.noOuterEnvironment := by
  exact P.selector.noOuterEnvironment_iff

theorem hasOuterEnvironment_iff (P : ParameterClosureStrong Cell T) :
    P.hasOuterEnvironment ↔ P.split.hasOuterEnvironment := by
  exact P.selector.hasOuterEnvironment_iff

theorem symmetrizedBoundaryOperator_transpose (P : ParameterClosureStrong Cell T) :
    Matrix.transpose P.symmetrizedBoundaryOperator = P.symmetrizedBoundaryOperator := by
  exact P.source.symmetrizedBoundaryOperator_transpose

theorem symmetrizedOperator_transpose (P : ParameterClosureStrong Cell T) :
    Matrix.transpose P.symmetrizedOperator = P.symmetrizedOperator := by
  exact P.source.symmetrizedOperator_transpose

theorem regularizationShift_eq_policy_canonicalShift (P : ParameterClosureStrong Cell T) :
    P.regularizationShift = P.regularizationPolicy.canonicalShift P.comparisonOperator := by
  exact P.source.regularizationShift_eq_policy_canonicalShift

theorem stabilizedOperator_eq_raw_plus_shift (P : ParameterClosureStrong Cell T) :
    P.stabilizedOperator =
      P.rawBoundaryOperator +
        P.regularizationShift • (1 : Matrix P.boundaryVertex P.boundaryVertex ℝ) := by
  exact P.source.stabilizedOperator_eq_raw_plus_shift

theorem stabilizedSymmetricOperator_transpose (P : ParameterClosureStrong Cell T) :
    Matrix.transpose P.stabilizedSymmetricOperator = P.stabilizedSymmetricOperator := by
  exact P.source.stabilizedSymmetricOperator_transpose

theorem stabilizedFlux_eq_mulVec
    (P : ParameterClosureStrong Cell T) (φ : P.boundaryPotential) :
    P.stabilizedFlux φ = (P.stabilizedOperator).mulVec φ := by
  exact P.source.stabilizedFlux_eq_mulVec φ

end ParameterClosureStrong

namespace StrengtheningS6

open CNNA.PillarA.Finite.StrengtheningS4
open CNNA.PillarA.DtN.StrengtheningS6

def referenceFullParameterClosure (b : Nat) (p : ConcretePolicyOf)
    (selector : BranchingSelectorStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p))
    (wp : WeightPolicy := CNNA.PillarA.Finite.StrengtheningS5.referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [CNNA.PillarA.DtN.StrengtheningS5.ReferenceInteriorEliminationData b p wp]
    : ParameterClosureStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ParameterClosureStrong.ofDtNAndSelector (referenceFullDtNStabilized b p wp rp) selector

def variationFullParameterClosure (β : Nat → Nat) (p : ConcretePolicyOf)
    (selector : BranchingSelectorStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p))
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [CNNA.PillarA.DtN.StrengtheningS5.VariationInteriorEliminationData β p wp]
    : ParameterClosureStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ParameterClosureStrong.ofDtNAndSelector (variationFullDtNStabilized β p wp rp) selector

end StrengtheningS6

end CNNA.PillarA.Closure
