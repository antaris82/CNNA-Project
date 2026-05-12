import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2cRGeneratedDegreeScaleSourceStatus where
  | generatedDegreeScaleSourceRequiredForTracePivotScaleWitness
  | generatedDegreeScaleSourceProvidedWithTwoSidedScaleEquations
  deriving DecidableEq, Repr

inductive SM3db2cRNoScalarInvStatus where
  | noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  deriving DecidableEq, Repr

inductive SM3db2cRNoMatrixInvStatus where
  | noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  deriving DecidableEq, Repr

inductive SM3db2cRNoExternalScaleOracleStatus where
  | noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  deriving DecidableEq, Repr

inductive SM3db2cRNoProductIdentityProofStatus where
  | noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  deriving DecidableEq, Repr

inductive SM3db2cRNoTwoSidedInvStatus where
  | noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  deriving DecidableEq, Repr

inductive SM3db2cRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  deriving DecidableEq, Repr

inductive SM3db2cRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  deriving DecidableEq, Repr

inductive SM3db2cRNextPhaseStatus where
  | generatedDegreeScaleSourceRequiredBeforeR3c1b1
  | sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  deriving DecidableEq, Repr

structure GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  sm3db2bRequirement :
    GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR Cell p A P wp W E K T
  sourceStatus : SM3db2cRGeneratedDegreeScaleSourceStatus
  noScalarInvStatus : SM3db2cRNoScalarInvStatus
  noMatrixInvStatus : SM3db2cRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2cRNoExternalScaleOracleStatus
  noProductIdentityProofStatus : SM3db2cRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2cRNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2cRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2cRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2cRNextPhaseStatus
  pivotEntry_eq_block :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedInteriorBlock W
          (T.localStepOf pivot).pivotDatum.pivotIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex
  pivotEntry_eq_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  sourceStatus_eq :
    sourceStatus =
      SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceRequiredForTracePivotScaleWitness
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2cRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2cRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2cRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2cRNextPhaseStatus.generatedDegreeScaleSourceRequiredBeforeR3c1b1

namespace GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}

def fromSM3db2bRequirement
    (R : GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T where
  sm3db2bRequirement := R
  sourceStatus :=
    SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceRequiredForTracePivotScaleWitness
  noScalarInvStatus :=
    SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus :=
    SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus :=
    SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  noProductIdentityProofStatus :=
    SM3db2cRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  noTwoSidedInvStatus :=
    SM3db2cRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  noDtnDataStatus :=
    SM3db2cRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  noArithmeticTargetStatus :=
    SM3db2cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  nextPhaseStatus := SM3db2cRNextPhaseStatus.generatedDegreeScaleSourceRequiredBeforeR3c1b1
  pivotEntry_eq_block := by
    intro pivot
    exact R.pivotEntry_eq_block pivot
  pivotEntry_eq_generatedDegree := by
    intro pivot
    exact R.pivotEntry_eq_dirichletDegree pivot
  sourceStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromSourceAudit
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T :=
  fromSM3db2bRequirement
    (GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR.fromSourceAudit A0)

theorem pivotEntry_bound_to_generatedDegree
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry =
      generatedDirichlet_degree W
        (GeneratedInteriorIndex.toApproximantIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex) :=
  R.pivotEntry_eq_generatedDegree pivot

theorem nextPhase_requires_generatedDegreeScaleSource
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T) :
    R.nextPhaseStatus = SM3db2cRNextPhaseStatus.generatedDegreeScaleSourceRequiredBeforeR3c1b1 :=
  R.nextPhaseStatus_eq

end GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR

structure GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  requirement : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T
  pivotScale : GeneratedInteriorIndex A → ℝ
  scaleSourceStatus : SM3db2cRGeneratedDegreeScaleSourceStatus
  noScalarInvStatus : SM3db2cRNoScalarInvStatus
  noMatrixInvStatus : SM3db2cRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2cRNoExternalScaleOracleStatus
  source_eq_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  pivotScale_mul_pivotEntry :
    ∀ pivot : GeneratedInteriorIndex A,
      pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1
  pivotEntry_mul_pivotScale :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry * pivotScale pivot = 1
  scaleSourceStatus_eq :
    scaleSourceStatus =
      SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceProvidedWithTwoSidedScaleEquations
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree

namespace GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}

def fromGeneratedDegreeScale
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T)
    (pivotScale : GeneratedInteriorIndex A → ℝ)
    (hLeft : ∀ pivot : GeneratedInteriorIndex A,
      pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1)
    (hRight : ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry * pivotScale pivot = 1) :
    GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T where
  requirement := R
  pivotScale := pivotScale
  scaleSourceStatus :=
    SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceProvidedWithTwoSidedScaleEquations
  noScalarInvStatus :=
    SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus :=
    SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus :=
    SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  source_eq_generatedDegree := by
    intro pivot
    exact R.pivotEntry_eq_generatedDegree pivot
  pivotScale_mul_pivotEntry := hLeft
  pivotEntry_mul_pivotScale := hRight
  scaleSourceStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl

theorem leftScaleEquation
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    S.pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1 :=
  S.pivotScale_mul_pivotEntry pivot

theorem rightScaleEquation
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry * S.pivotScale pivot = 1 :=
  S.pivotEntry_mul_pivotScale pivot

theorem source_eq_generatedDegree_of
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry =
      generatedDirichlet_degree W
        (GeneratedInteriorIndex.toApproximantIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex) :=
  S.source_eq_generatedDegree pivot

end GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR


def generatedInteriorTracePivotScaleWitnessFromGeneratedDegreeScaleSourceSM3db2cR
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T where
  requirement := S.requirement.sm3db2bRequirement
  pivotScale := S.pivotScale
  pivotScale_mul_pivotEntry := S.pivotScale_mul_pivotEntry
  pivotEntry_mul_pivotScale := S.pivotEntry_mul_pivotScale
  pivotScaleSourceStatus :=
    SM3db2bRPivotScaleSourceStatus.pivotScaleWitnessMustComeFromGeneratedDegreeProfile
  pivotScaleSourceStatus_eq := by
    rfl

def generatedInteriorPerPivotRegularityFromGeneratedDegreeScaleSourceSM3db2cR
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T) :
    GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T :=
  GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR.fromTracePivotScaleWitness
    (generatedInteriorTracePivotScaleWitnessFromGeneratedDegreeScaleSourceSM3db2cR S)

structure GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  scaleSource : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T
  tracePivotScaleWitness : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T
  perPivotRegularity : GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T
  sourceStatus : SM3db2cRGeneratedDegreeScaleSourceStatus
  noScalarInvStatus : SM3db2cRNoScalarInvStatus
  noMatrixInvStatus : SM3db2cRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2cRNoExternalScaleOracleStatus
  noProductIdentityProofStatus : SM3db2cRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2cRNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2cRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2cRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2cRNextPhaseStatus
  tracePivotScaleWitness_eq_from_generatedDegreeScaleSource :
    tracePivotScaleWitness =
      generatedInteriorTracePivotScaleWitnessFromGeneratedDegreeScaleSourceSM3db2cR scaleSource
  perPivotRegularity_eq_from_tracePivotScaleWitness :
    perPivotRegularity =
      GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR.fromTracePivotScaleWitness
        tracePivotScaleWitness
  sourceStatus_eq :
    sourceStatus =
      SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceProvidedWithTwoSidedScaleEquations
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2cRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2cRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2cRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2cRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge

namespace GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}

def fromGeneratedDegreeScaleSource
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR Cell p A P wp W E K T where
  scaleSource := S
  tracePivotScaleWitness :=
    generatedInteriorTracePivotScaleWitnessFromGeneratedDegreeScaleSourceSM3db2cR S
  perPivotRegularity :=
    generatedInteriorPerPivotRegularityFromGeneratedDegreeScaleSourceSM3db2cR S
  sourceStatus :=
    SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceProvidedWithTwoSidedScaleEquations
  noScalarInvStatus :=
    SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus :=
    SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus :=
    SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  noProductIdentityProofStatus :=
    SM3db2cRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  noTwoSidedInvStatus :=
    SM3db2cRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  noDtnDataStatus := SM3db2cRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  noArithmeticTargetStatus :=
    SM3db2cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  nextPhaseStatus := SM3db2cRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  tracePivotScaleWitness_eq_from_generatedDegreeScaleSource := by
    rfl
  perPivotRegularity_eq_from_tracePivotScaleWitness := by
    rfl
  sourceStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem tracePivotScaleWitness_left_inverse
    (G : GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    G.tracePivotScaleWitness.pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1 :=
  G.tracePivotScaleWitness.pivotScale_mul_pivotEntry pivot

theorem tracePivotScaleWitness_right_inverse
    (G : GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry * G.tracePivotScaleWitness.pivotScale pivot = 1 :=
  G.tracePivotScaleWitness.pivotEntry_mul_pivotScale pivot

theorem nextPhase_is_r3c1b1
    (G : GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR Cell p A P wp W E K T) :
    G.nextPhaseStatus = SM3db2cRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge :=
  G.nextPhaseStatus_eq

end GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR

structure GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  requirement : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T
  sourceStatus : SM3db2cRGeneratedDegreeScaleSourceStatus
  noScalarInvStatus : SM3db2cRNoScalarInvStatus
  noMatrixInvStatus : SM3db2cRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2cRNoExternalScaleOracleStatus
  noProductIdentityProofStatus : SM3db2cRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2cRNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2cRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2cRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2cRNextPhaseStatus
  sourceStatus_eq :
    sourceStatus =
      SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceRequiredForTracePivotScaleWitness
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2cRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2cRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2cRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2cRNextPhaseStatus.generatedDegreeScaleSourceRequiredBeforeR3c1b1

namespace GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}

def fromRequirement
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR Cell p A P wp W E K T where
  requirement := R
  sourceStatus :=
    SM3db2cRGeneratedDegreeScaleSourceStatus.generatedDegreeScaleSourceRequiredForTracePivotScaleWitness
  noScalarInvStatus :=
    SM3db2cRNoScalarInvStatus.noScalarInvInTracePivotScaleWitnessFromGeneratedDegree
  noMatrixInvStatus :=
    SM3db2cRNoMatrixInvStatus.noMatrixInvInTracePivotScaleWitnessFromGeneratedDegree
  noExternalScaleOracleStatus :=
    SM3db2cRNoExternalScaleOracleStatus.noExternalScaleOracleInTracePivotScaleWitnessFromGeneratedDegree
  noProductIdentityProofStatus :=
    SM3db2cRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotScaleWitnessFromGeneratedDegree
  noTwoSidedInvStatus :=
    SM3db2cRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotScaleWitnessFromGeneratedDegree
  noDtnDataStatus := SM3db2cRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2cR
  noArithmeticTargetStatus :=
    SM3db2cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2cR
  nextPhaseStatus := SM3db2cRNextPhaseStatus.generatedDegreeScaleSourceRequiredBeforeR3c1b1
  sourceStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromSourceAudit
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR Cell p A P wp W E K T :=
  fromRequirement
    (GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR.fromSourceAudit A0)

theorem nextPhase_requires_generatedDegreeScaleSource
    (A0 : GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR Cell p A P wp W E K T) :
    A0.nextPhaseStatus = SM3db2cRNextPhaseStatus.generatedDegreeScaleSourceRequiredBeforeR3c1b1 :=
  A0.nextPhaseStatus_eq

end GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR

abbrev RegularGeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

end Smoke

end CNNA.PillarA.Arithmetic
