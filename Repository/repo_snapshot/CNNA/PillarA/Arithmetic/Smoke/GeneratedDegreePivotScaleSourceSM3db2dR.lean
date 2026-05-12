import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2dRGeneratedDegreeReciprocalProfileStatus where
  | generatedDegreeReciprocalProfileRequired
  | generatedDegreeReciprocalProfileProvided
  deriving DecidableEq, Repr

inductive SM3db2dRScaleSourceStatus where
  | scaleSourceBuiltFromGeneratedDegreeReciprocalProfile
  deriving DecidableEq, Repr

inductive SM3db2dRNoScalarInvStatus where
  | noScalarInvInGeneratedDegreePivotScaleSource
  deriving DecidableEq, Repr

inductive SM3db2dRNoMatrixInvStatus where
  | noMatrixInvInGeneratedDegreePivotScaleSource
  deriving DecidableEq, Repr

inductive SM3db2dRNoExternalScaleOracleStatus where
  | noExternalScaleOracleInGeneratedDegreePivotScaleSource
  deriving DecidableEq, Repr

inductive SM3db2dRNoProductIdentityProofStatus where
  | noProductIdentityProofInGeneratedDegreePivotScaleSource
  deriving DecidableEq, Repr

inductive SM3db2dRNoTwoSidedInvStatus where
  | noTwoSidedInvInGeneratedDegreePivotScaleSource
  deriving DecidableEq, Repr

inductive SM3db2dRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2dR
  deriving DecidableEq, Repr

inductive SM3db2dRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2dR
  deriving DecidableEq, Repr

inductive SM3db2dRNextPhaseStatus where
  | generatedDegreeReciprocalProfileStillRequired
  | sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  deriving DecidableEq, Repr

structure GeneratedDegreePivotReciprocalProfileSM3db2dR
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
  generatedDegreePivotScale : GeneratedInteriorIndex A → ℝ
  profileStatus : SM3db2dRGeneratedDegreeReciprocalProfileStatus
  noScalarInvStatus : SM3db2dRNoScalarInvStatus
  noMatrixInvStatus : SM3db2dRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2dRNoExternalScaleOracleStatus
  source_eq_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  generatedDegreePivotScale_mul_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      generatedDegreePivotScale pivot *
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) = 1
  generatedDegree_mul_generatedDegreePivotScale :
    ∀ pivot : GeneratedInteriorIndex A,
      generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) *
          generatedDegreePivotScale pivot = 1
  profileStatus_eq :
    profileStatus =
      SM3db2dRGeneratedDegreeReciprocalProfileStatus.generatedDegreeReciprocalProfileProvided
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2dRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotScaleSource
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2dRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotScaleSource
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2dRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotScaleSource

namespace GeneratedDegreePivotReciprocalProfileSM3db2dR

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

def fromGeneratedDegreeReciprocalProfile
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T)
    (generatedDegreePivotScale : GeneratedInteriorIndex A → ℝ)
    (hLeftDegree : ∀ pivot : GeneratedInteriorIndex A,
      generatedDegreePivotScale pivot *
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) = 1)
    (hRightDegree : ∀ pivot : GeneratedInteriorIndex A,
      generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) *
          generatedDegreePivotScale pivot = 1) :
    GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T where
  requirement := R
  generatedDegreePivotScale := generatedDegreePivotScale
  profileStatus :=
    SM3db2dRGeneratedDegreeReciprocalProfileStatus.generatedDegreeReciprocalProfileProvided
  noScalarInvStatus :=
    SM3db2dRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotScaleSource
  noMatrixInvStatus :=
    SM3db2dRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotScaleSource
  noExternalScaleOracleStatus :=
    SM3db2dRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotScaleSource
  source_eq_generatedDegree := by
    intro pivot
    exact R.pivotEntry_eq_generatedDegree pivot
  generatedDegreePivotScale_mul_generatedDegree := hLeftDegree
  generatedDegree_mul_generatedDegreePivotScale := hRightDegree
  profileStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl

theorem leftGeneratedDegreeEquation
    (D : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    D.generatedDegreePivotScale pivot *
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex) = 1 :=
  D.generatedDegreePivotScale_mul_generatedDegree pivot

theorem rightGeneratedDegreeEquation
    (D : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex) *
        D.generatedDegreePivotScale pivot = 1 :=
  D.generatedDegree_mul_generatedDegreePivotScale pivot

theorem source_eq_generatedDegree_of
    (D : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry =
      generatedDirichlet_degree W
        (GeneratedInteriorIndex.toApproximantIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex) :=
  D.source_eq_generatedDegree pivot

end GeneratedDegreePivotReciprocalProfileSM3db2dR

def generatedDegreePivotScaleSourceFromReciprocalProfileSM3db2dR
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
    (D : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T) :
    GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T :=
  GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR.fromGeneratedDegreeScale
    D.requirement
    D.generatedDegreePivotScale
    (by
      intro pivot
      calc
        D.generatedDegreePivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry
            = D.generatedDegreePivotScale pivot *
                generatedDirichlet_degree W
                  (GeneratedInteriorIndex.toApproximantIndex
                    (T.localStepOf pivot).pivotDatum.pivotIndex) := by
              rw [D.source_eq_generatedDegree pivot]
        _ = 1 := D.generatedDegreePivotScale_mul_generatedDegree pivot)
    (by
      intro pivot
      calc
        (T.localStepOf pivot).stepUpdate.pivotEntry * D.generatedDegreePivotScale pivot
            = generatedDirichlet_degree W
                  (GeneratedInteriorIndex.toApproximantIndex
                    (T.localStepOf pivot).pivotDatum.pivotIndex) *
                D.generatedDegreePivotScale pivot := by
              rw [D.source_eq_generatedDegree pivot]
        _ = 1 := D.generatedDegree_mul_generatedDegreePivotScale pivot)

structure GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR
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
  reciprocalProfile : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T
  sm3db2cScaleSource : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2cR Cell p A P wp W E K T
  scaleSourceStatus : SM3db2dRScaleSourceStatus
  noScalarInvStatus : SM3db2dRNoScalarInvStatus
  noMatrixInvStatus : SM3db2dRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2dRNoExternalScaleOracleStatus
  noProductIdentityProofStatus : SM3db2dRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2dRNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2dRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2dRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2dRNextPhaseStatus
  sm3db2cScaleSource_eq_from_reciprocalProfile :
    sm3db2cScaleSource =
      generatedDegreePivotScaleSourceFromReciprocalProfileSM3db2dR reciprocalProfile
  scaleSourceStatus_eq :
    scaleSourceStatus =
      SM3db2dRScaleSourceStatus.scaleSourceBuiltFromGeneratedDegreeReciprocalProfile
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2dRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotScaleSource
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2dRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotScaleSource
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2dRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotScaleSource
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2dRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotScaleSource
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2dRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotScaleSource
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2dR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2dR
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3db2dRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge

namespace GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR

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

def fromReciprocalProfile
    (D : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T) :
    GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T where
  reciprocalProfile := D
  sm3db2cScaleSource := generatedDegreePivotScaleSourceFromReciprocalProfileSM3db2dR D
  scaleSourceStatus :=
    SM3db2dRScaleSourceStatus.scaleSourceBuiltFromGeneratedDegreeReciprocalProfile
  noScalarInvStatus :=
    SM3db2dRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotScaleSource
  noMatrixInvStatus :=
    SM3db2dRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotScaleSource
  noExternalScaleOracleStatus :=
    SM3db2dRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotScaleSource
  noProductIdentityProofStatus :=
    SM3db2dRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotScaleSource
  noTwoSidedInvStatus :=
    SM3db2dRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotScaleSource
  noDtnDataStatus := SM3db2dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2dR
  noArithmeticTargetStatus :=
    SM3db2dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2dR
  nextPhaseStatus := SM3db2dRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  sm3db2cScaleSource_eq_from_reciprocalProfile := by
    rfl
  scaleSourceStatus_eq := by
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

theorem leftScaleEquation
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    S.sm3db2cScaleSource.pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1 :=
  S.sm3db2cScaleSource.pivotScale_mul_pivotEntry pivot

theorem rightScaleEquation
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry * S.sm3db2cScaleSource.pivotScale pivot = 1 :=
  S.sm3db2cScaleSource.pivotEntry_mul_pivotScale pivot

theorem nextPhase_is_r3c1b1
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T) :
    S.nextPhaseStatus =
      SM3db2dRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge :=
  S.nextPhaseStatus_eq

end GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR

def tracePivotScaleWitness_from_generatedDegreePivotScaleSourceSM3db2dR
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
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T :=
  generatedInteriorTracePivotScaleWitnessFromGeneratedDegreeScaleSourceSM3db2cR
    S.sm3db2cScaleSource

def tracePivotScaleWitnessFromGeneratedDegree_from_sm3db2dR
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
    (S : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR Cell p A P wp W E K T :=
  GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR.fromGeneratedDegreeScaleSource
    S.sm3db2cScaleSource

structure GeneratedDegreePivotScaleSourceAuditSM3db2dR
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
  profileStatus : SM3db2dRGeneratedDegreeReciprocalProfileStatus
  noScalarInvStatus : SM3db2dRNoScalarInvStatus
  noMatrixInvStatus : SM3db2dRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2dRNoExternalScaleOracleStatus
  noProductIdentityProofStatus : SM3db2dRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2dRNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2dRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2dRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2dRNextPhaseStatus
  source_eq_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  profileStatus_eq :
    profileStatus =
      SM3db2dRGeneratedDegreeReciprocalProfileStatus.generatedDegreeReciprocalProfileRequired
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2dRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotScaleSource
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2dRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotScaleSource
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2dRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotScaleSource
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2dRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotScaleSource
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2dRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotScaleSource
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2dR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2dR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2dRNextPhaseStatus.generatedDegreeReciprocalProfileStillRequired

namespace GeneratedDegreePivotScaleSourceAuditSM3db2dR

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
    GeneratedDegreePivotScaleSourceAuditSM3db2dR Cell p A P wp W E K T where
  requirement := R
  profileStatus :=
    SM3db2dRGeneratedDegreeReciprocalProfileStatus.generatedDegreeReciprocalProfileRequired
  noScalarInvStatus :=
    SM3db2dRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotScaleSource
  noMatrixInvStatus :=
    SM3db2dRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotScaleSource
  noExternalScaleOracleStatus :=
    SM3db2dRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotScaleSource
  noProductIdentityProofStatus :=
    SM3db2dRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotScaleSource
  noTwoSidedInvStatus :=
    SM3db2dRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotScaleSource
  noDtnDataStatus := SM3db2dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2dR
  noArithmeticTargetStatus :=
    SM3db2dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2dR
  nextPhaseStatus := SM3db2dRNextPhaseStatus.generatedDegreeReciprocalProfileStillRequired
  source_eq_generatedDegree := by
    intro pivot
    exact R.pivotEntry_eq_generatedDegree pivot
  profileStatus_eq := by
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

def fromSM3db2cAudit
    (A0 : GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeAuditSM3db2cR Cell p A P wp W E K T) :
    GeneratedDegreePivotScaleSourceAuditSM3db2dR Cell p A P wp W E K T :=
  fromRequirement A0.requirement

theorem nextPhase_requires_generatedDegreeReciprocalProfile
    (A0 : GeneratedDegreePivotScaleSourceAuditSM3db2dR Cell p A P wp W E K T) :
    A0.nextPhaseStatus = SM3db2dRNextPhaseStatus.generatedDegreeReciprocalProfileStillRequired :=
  A0.nextPhaseStatus_eq

end GeneratedDegreePivotScaleSourceAuditSM3db2dR

abbrev RegularGeneratedDegreePivotReciprocalProfileSM3db2dR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreePivotReciprocalProfileSM3db2dR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedDegreePivotReciprocalProfileSM3db2dR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreePivotReciprocalProfileSM3db2dR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedDegreePivotScaleSourceAuditSM3db2dR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreePivotScaleSourceAuditSM3db2dR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedDegreePivotScaleSourceAuditSM3db2dR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreePivotScaleSourceAuditSM3db2dR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

end Smoke

end CNNA.PillarA.Arithmetic
