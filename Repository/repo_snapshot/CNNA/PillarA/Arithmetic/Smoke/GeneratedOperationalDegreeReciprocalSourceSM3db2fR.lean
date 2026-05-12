import CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR
import CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2fROperationalDegreeReciprocalDatumStatus where
  | operationalDegreeReciprocalDatumProvided
  deriving DecidableEq, Repr

inductive SM3db2fRWeightPolicyDegreeFormulaStatus where
  | weightPolicyDegreeFormulaCarriedFromSM3db2eR
  deriving DecidableEq, Repr

inductive SM3db2fRReciprocalProfileStatus where
  | reciprocalProfileBuiltFromOperationalDegreeSource
  deriving DecidableEq, Repr

inductive SM3db2fRTracePivotScaleWitnessStatus where
  | tracePivotScaleWitnessExportedThroughSM3db2dRSM3db2cRSM3db2bR
  deriving DecidableEq, Repr

inductive SM3db2fRNoScalarInvStatus where
  | noScalarInvInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoMatrixInvStatus where
  | noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoExternalScaleOracleStatus where
  | noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoFreeScaleTableStatus where
  | noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoProductIdentityProofStatus where
  | noProductIdentityProofInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoTwoSidedInvStatus where
  | noTwoSidedInvInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

inductive SM3db2fRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2fR
  deriving DecidableEq, Repr

inductive SM3db2fRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2fR
  deriving DecidableEq, Repr

inductive SM3db2fRNextPhaseStatus where
  | sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  deriving DecidableEq, Repr

structure GeneratedOperationalDegreeReciprocalDatumSM3db2fR
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
  sm3db2eRAttempt :
    GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T
  degreePivotScale : GeneratedInteriorIndex A → ℝ
  datumStatus : SM3db2fROperationalDegreeReciprocalDatumStatus
  weightPolicyDegreeFormulaStatus : SM3db2fRWeightPolicyDegreeFormulaStatus
  noScalarInvStatus : SM3db2fRNoScalarInvStatus
  noMatrixInvStatus : SM3db2fRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2fRNoExternalScaleOracleStatus
  noFreeScaleTableStatus : SM3db2fRNoFreeScaleTableStatus
  degree_eq_inputPolicyAdjacencyWeight_sum :
    ∀ i : GeneratedApproximantIndex A,
      generatedDirichlet_degree W i =
        ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent i j then wp.constantWeight i j else 0
  pivotEntry_eq_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  pivotEntry_eq_inputPolicyAdjacencyWeight_sum :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent
              (GeneratedInteriorIndex.toApproximantIndex
                (T.localStepOf pivot).pivotDatum.pivotIndex)
              j then
            wp.constantWeight
              (GeneratedInteriorIndex.toApproximantIndex
                (T.localStepOf pivot).pivotDatum.pivotIndex)
              j
          else 0
  degreePivotScale_mul_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      degreePivotScale pivot *
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) = 1
  generatedDegree_mul_degreePivotScale :
    ∀ pivot : GeneratedInteriorIndex A,
      generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) *
          degreePivotScale pivot = 1
  sm3db2eR_profileConstructionStatus_eq :
    sm3db2eRAttempt.profileConstructionStatus =
      SM3db2eRProfileConstructionStatus.generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI
  sm3db2eR_nextPhaseStatus_eq :
    sm3db2eRAttempt.nextPhaseStatus =
      SM3db2eRNextPhaseStatus.sm3db2fRGeneratedOperationalDegreeReciprocalSource
  datumStatus_eq :
    datumStatus =
      SM3db2fROperationalDegreeReciprocalDatumStatus.operationalDegreeReciprocalDatumProvided
  weightPolicyDegreeFormulaStatus_eq :
    weightPolicyDegreeFormulaStatus =
      SM3db2fRWeightPolicyDegreeFormulaStatus.weightPolicyDegreeFormulaCarriedFromSM3db2eR
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2fRNoScalarInvStatus.noScalarInvInGeneratedOperationalDegreeReciprocalSource
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2fRNoMatrixInvStatus.noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2fRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  noFreeScaleTableStatus_eq :
    noFreeScaleTableStatus =
      SM3db2fRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource

namespace GeneratedOperationalDegreeReciprocalDatumSM3db2fR

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

def fromSM3db2eRAttempt
    (D : GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T)
    (degreePivotScale : GeneratedInteriorIndex A → ℝ)
    (hLeftDegree : ∀ pivot : GeneratedInteriorIndex A,
      degreePivotScale pivot *
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) = 1)
    (hRightDegree : ∀ pivot : GeneratedInteriorIndex A,
      generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) *
          degreePivotScale pivot = 1) :
    GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T where
  sm3db2eRAttempt := D
  degreePivotScale := degreePivotScale
  datumStatus :=
    SM3db2fROperationalDegreeReciprocalDatumStatus.operationalDegreeReciprocalDatumProvided
  weightPolicyDegreeFormulaStatus :=
    SM3db2fRWeightPolicyDegreeFormulaStatus.weightPolicyDegreeFormulaCarriedFromSM3db2eR
  noScalarInvStatus :=
    SM3db2fRNoScalarInvStatus.noScalarInvInGeneratedOperationalDegreeReciprocalSource
  noMatrixInvStatus :=
    SM3db2fRNoMatrixInvStatus.noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  noExternalScaleOracleStatus :=
    SM3db2fRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  noFreeScaleTableStatus :=
    SM3db2fRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource
  degree_eq_inputPolicyAdjacencyWeight_sum := by
    intro i
    exact D.degree_eq_inputPolicyAdjacencyWeight_sum i
  pivotEntry_eq_generatedDegree := by
    intro pivot
    exact D.pivotEntry_eq_generatedDegree pivot
  pivotEntry_eq_inputPolicyAdjacencyWeight_sum := by
    intro pivot
    exact D.pivotEntry_eq_inputPolicyAdjacencyWeight_sum pivot
  degreePivotScale_mul_generatedDegree := hLeftDegree
  generatedDegree_mul_degreePivotScale := hRightDegree
  sm3db2eR_profileConstructionStatus_eq := D.profileConstructionStatus_eq
  sm3db2eR_nextPhaseStatus_eq := D.nextPhaseStatus_eq
  datumStatus_eq := by
    rfl
  weightPolicyDegreeFormulaStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl
  noFreeScaleTableStatus_eq := by
    rfl

theorem leftGeneratedDegreeEquation
    (O : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    O.degreePivotScale pivot *
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex) = 1 :=
  O.degreePivotScale_mul_generatedDegree pivot

theorem rightGeneratedDegreeEquation
    (O : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex) *
        O.degreePivotScale pivot = 1 :=
  O.generatedDegree_mul_degreePivotScale pivot

theorem pivotEntry_eq_generatedDegree_of
    (O : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry =
      generatedDirichlet_degree W
        (GeneratedInteriorIndex.toApproximantIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex) :=
  O.pivotEntry_eq_generatedDegree pivot

theorem weightPolicyDegreeFormula_of
    (O : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T)
    (i : GeneratedApproximantIndex A) :
    generatedDirichlet_degree W i =
      ∑ j : GeneratedApproximantIndex A,
        if generatedAdjacent i j then wp.constantWeight i j else 0 :=
  O.degree_eq_inputPolicyAdjacencyWeight_sum i

end GeneratedOperationalDegreeReciprocalDatumSM3db2fR

def generatedDegreePivotReciprocalProfileFromOperationalDatumSM3db2fR
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
    (O : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T) :
    GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T :=
  GeneratedDegreePivotReciprocalProfileSM3db2dR.fromGeneratedDegreeReciprocalProfile
    O.sm3db2eRAttempt.audit.requirement
    O.degreePivotScale
    O.degreePivotScale_mul_generatedDegree
    O.generatedDegree_mul_degreePivotScale

structure GeneratedOperationalDegreeReciprocalSourceSM3db2fR
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
  operationalDatum : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T
  reciprocalProfile : GeneratedDegreePivotReciprocalProfileSM3db2dR Cell p A P wp W E K T
  sm3db2dScaleSource : GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR Cell p A P wp W E K T
  tracePivotScaleWitness : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T
  reciprocalProfileStatus : SM3db2fRReciprocalProfileStatus
  tracePivotScaleWitnessStatus : SM3db2fRTracePivotScaleWitnessStatus
  noScalarInvStatus : SM3db2fRNoScalarInvStatus
  noMatrixInvStatus : SM3db2fRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2fRNoExternalScaleOracleStatus
  noFreeScaleTableStatus : SM3db2fRNoFreeScaleTableStatus
  noProductIdentityProofStatus : SM3db2fRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2fRNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db2fRNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db2fRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2fRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2fRNextPhaseStatus
  reciprocalProfile_eq_from_operationalDatum :
    reciprocalProfile =
      generatedDegreePivotReciprocalProfileFromOperationalDatumSM3db2fR operationalDatum
  sm3db2dScaleSource_eq_from_reciprocalProfile :
    sm3db2dScaleSource =
      GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR.fromReciprocalProfile
        reciprocalProfile
  tracePivotScaleWitness_eq_from_sm3db2dScaleSource :
    tracePivotScaleWitness =
      tracePivotScaleWitness_from_generatedDegreePivotScaleSourceSM3db2dR sm3db2dScaleSource
  reciprocalProfileStatus_eq :
    reciprocalProfileStatus =
      SM3db2fRReciprocalProfileStatus.reciprocalProfileBuiltFromOperationalDegreeSource
  tracePivotScaleWitnessStatus_eq :
    tracePivotScaleWitnessStatus =
      SM3db2fRTracePivotScaleWitnessStatus.tracePivotScaleWitnessExportedThroughSM3db2dRSM3db2cRSM3db2bR
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2fRNoScalarInvStatus.noScalarInvInGeneratedOperationalDegreeReciprocalSource
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2fRNoMatrixInvStatus.noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2fRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  noFreeScaleTableStatus_eq :
    noFreeScaleTableStatus =
      SM3db2fRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2fRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedOperationalDegreeReciprocalSource
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2fRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedOperationalDegreeReciprocalSource
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db2fRNoInteriorEliminationDataStatus.noInteriorEliminationDataInGeneratedOperationalDegreeReciprocalSource
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2fRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2fR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2fRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2fR
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3db2fRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge

namespace GeneratedOperationalDegreeReciprocalSourceSM3db2fR

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

def fromOperationalDatum
    (O : GeneratedOperationalDegreeReciprocalDatumSM3db2fR Cell p A P wp W E K T) :
    GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T where
  operationalDatum := O
  reciprocalProfile := generatedDegreePivotReciprocalProfileFromOperationalDatumSM3db2fR O
  sm3db2dScaleSource :=
    GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR.fromReciprocalProfile
      (generatedDegreePivotReciprocalProfileFromOperationalDatumSM3db2fR O)
  tracePivotScaleWitness :=
    tracePivotScaleWitness_from_generatedDegreePivotScaleSourceSM3db2dR
      (GeneratedInteriorGeneratedDegreePivotScaleSourceSM3db2dR.fromReciprocalProfile
        (generatedDegreePivotReciprocalProfileFromOperationalDatumSM3db2fR O))
  reciprocalProfileStatus :=
    SM3db2fRReciprocalProfileStatus.reciprocalProfileBuiltFromOperationalDegreeSource
  tracePivotScaleWitnessStatus :=
    SM3db2fRTracePivotScaleWitnessStatus.tracePivotScaleWitnessExportedThroughSM3db2dRSM3db2cRSM3db2bR
  noScalarInvStatus :=
    SM3db2fRNoScalarInvStatus.noScalarInvInGeneratedOperationalDegreeReciprocalSource
  noMatrixInvStatus :=
    SM3db2fRNoMatrixInvStatus.noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  noExternalScaleOracleStatus :=
    SM3db2fRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  noFreeScaleTableStatus :=
    SM3db2fRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource
  noProductIdentityProofStatus :=
    SM3db2fRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedOperationalDegreeReciprocalSource
  noTwoSidedInvStatus :=
    SM3db2fRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedOperationalDegreeReciprocalSource
  noInteriorEliminationDataStatus :=
    SM3db2fRNoInteriorEliminationDataStatus.noInteriorEliminationDataInGeneratedOperationalDegreeReciprocalSource
  noDtnDataStatus := SM3db2fRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2fR
  noArithmeticTargetStatus :=
    SM3db2fRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2fR
  nextPhaseStatus := SM3db2fRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  reciprocalProfile_eq_from_operationalDatum := by
    rfl
  sm3db2dScaleSource_eq_from_reciprocalProfile := by
    rfl
  tracePivotScaleWitness_eq_from_sm3db2dScaleSource := by
    rfl
  reciprocalProfileStatus_eq := by
    rfl
  tracePivotScaleWitnessStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl
  noFreeScaleTableStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem leftScaleEquation
    (S : GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    S.sm3db2dScaleSource.sm3db2cScaleSource.pivotScale pivot *
        (T.localStepOf pivot).stepUpdate.pivotEntry = 1 :=
  S.sm3db2dScaleSource.sm3db2cScaleSource.pivotScale_mul_pivotEntry pivot

theorem rightScaleEquation
    (S : GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry *
        S.sm3db2dScaleSource.sm3db2cScaleSource.pivotScale pivot = 1 :=
  S.sm3db2dScaleSource.sm3db2cScaleSource.pivotEntry_mul_pivotScale pivot

theorem nextPhase_is_r3c1b1
    (S : GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T) :
    S.nextPhaseStatus =
      SM3db2fRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge :=
  S.nextPhaseStatus_eq

end GeneratedOperationalDegreeReciprocalSourceSM3db2fR

def generatedOperationalDegreeReciprocalSource_from_weightPolicy
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
    (D : GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T)
    (degreePivotScale : GeneratedInteriorIndex A → ℝ)
    (hLeftDegree : ∀ pivot : GeneratedInteriorIndex A,
      degreePivotScale pivot *
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) = 1)
    (hRightDegree : ∀ pivot : GeneratedInteriorIndex A,
      generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) *
          degreePivotScale pivot = 1) :
    GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T :=
  GeneratedOperationalDegreeReciprocalSourceSM3db2fR.fromOperationalDatum
    (GeneratedOperationalDegreeReciprocalDatumSM3db2fR.fromSM3db2eRAttempt
      D degreePivotScale hLeftDegree hRightDegree)

def tracePivotScaleWitness_from_generatedOperationalDegreeReciprocalSourceSM3db2fR
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
    (S : GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T :=
  S.tracePivotScaleWitness

abbrev RegularGeneratedOperationalDegreeReciprocalDatumSM3db2fR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedOperationalDegreeReciprocalDatumSM3db2fR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedOperationalDegreeReciprocalDatumSM3db2fR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedOperationalDegreeReciprocalDatumSM3db2fR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedOperationalDegreeReciprocalSourceSM3db2fR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedOperationalDegreeReciprocalSourceSM3db2fR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3db2fRGeneratedOperationalDegreeReciprocalSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularSource : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p regularWeight
  variableSource : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p variableWeight
  regularNoScalarInvStatus_eq :
    regularSource.noScalarInvStatus =
      SM3db2fRNoScalarInvStatus.noScalarInvInGeneratedOperationalDegreeReciprocalSource
  variableNoScalarInvStatus_eq :
    variableSource.noScalarInvStatus =
      SM3db2fRNoScalarInvStatus.noScalarInvInGeneratedOperationalDegreeReciprocalSource
  regularNoMatrixInvStatus_eq :
    regularSource.noMatrixInvStatus =
      SM3db2fRNoMatrixInvStatus.noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  variableNoMatrixInvStatus_eq :
    variableSource.noMatrixInvStatus =
      SM3db2fRNoMatrixInvStatus.noMatrixInvInGeneratedOperationalDegreeReciprocalSource
  regularNoExternalScaleOracleStatus_eq :
    regularSource.noExternalScaleOracleStatus =
      SM3db2fRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  variableNoExternalScaleOracleStatus_eq :
    variableSource.noExternalScaleOracleStatus =
      SM3db2fRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedOperationalDegreeReciprocalSource
  regularNoFreeScaleTableStatus_eq :
    regularSource.noFreeScaleTableStatus =
      SM3db2fRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource
  variableNoFreeScaleTableStatus_eq :
    variableSource.noFreeScaleTableStatus =
      SM3db2fRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedOperationalDegreeReciprocalSource
  regularNoProductIdentityProofStatus_eq :
    regularSource.noProductIdentityProofStatus =
      SM3db2fRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedOperationalDegreeReciprocalSource
  variableNoProductIdentityProofStatus_eq :
    variableSource.noProductIdentityProofStatus =
      SM3db2fRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedOperationalDegreeReciprocalSource
  regularNoTwoSidedInvStatus_eq :
    regularSource.noTwoSidedInvStatus =
      SM3db2fRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedOperationalDegreeReciprocalSource
  variableNoTwoSidedInvStatus_eq :
    variableSource.noTwoSidedInvStatus =
      SM3db2fRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedOperationalDegreeReciprocalSource
  regularNoInteriorEliminationDataStatus_eq :
    regularSource.noInteriorEliminationDataStatus =
      SM3db2fRNoInteriorEliminationDataStatus.noInteriorEliminationDataInGeneratedOperationalDegreeReciprocalSource
  variableNoInteriorEliminationDataStatus_eq :
    variableSource.noInteriorEliminationDataStatus =
      SM3db2fRNoInteriorEliminationDataStatus.noInteriorEliminationDataInGeneratedOperationalDegreeReciprocalSource
  regularNoDtnDataStatus_eq :
    regularSource.noDtnDataStatus =
      SM3db2fRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2fR
  variableNoDtnDataStatus_eq :
    variableSource.noDtnDataStatus =
      SM3db2fRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2fR
  regularNoArithmeticTargetStatus_eq :
    regularSource.noArithmeticTargetStatus =
      SM3db2fRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2fR
  variableNoArithmeticTargetStatus_eq :
    variableSource.noArithmeticTargetStatus =
      SM3db2fRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2fR
  regularNextPhaseStatus_eq :
    regularSource.nextPhaseStatus =
      SM3db2fRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  variableNextPhaseStatus_eq :
    variableSource.nextPhaseStatus =
      SM3db2fRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge

namespace SM3db2fRGeneratedOperationalDegreeReciprocalSourceLedger

def fromRegularAndVariable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularSource : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p regularWeight)
    (variableSource : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p variableWeight) :
    SM3db2fRGeneratedOperationalDegreeReciprocalSourceLedger b β p regularWeight variableWeight where
  regularSource := regularSource
  variableSource := variableSource
  regularNoScalarInvStatus_eq := regularSource.noScalarInvStatus_eq
  variableNoScalarInvStatus_eq := variableSource.noScalarInvStatus_eq
  regularNoMatrixInvStatus_eq := regularSource.noMatrixInvStatus_eq
  variableNoMatrixInvStatus_eq := variableSource.noMatrixInvStatus_eq
  regularNoExternalScaleOracleStatus_eq := regularSource.noExternalScaleOracleStatus_eq
  variableNoExternalScaleOracleStatus_eq := variableSource.noExternalScaleOracleStatus_eq
  regularNoFreeScaleTableStatus_eq := regularSource.noFreeScaleTableStatus_eq
  variableNoFreeScaleTableStatus_eq := variableSource.noFreeScaleTableStatus_eq
  regularNoProductIdentityProofStatus_eq := regularSource.noProductIdentityProofStatus_eq
  variableNoProductIdentityProofStatus_eq := variableSource.noProductIdentityProofStatus_eq
  regularNoTwoSidedInvStatus_eq := regularSource.noTwoSidedInvStatus_eq
  variableNoTwoSidedInvStatus_eq := variableSource.noTwoSidedInvStatus_eq
  regularNoInteriorEliminationDataStatus_eq := regularSource.noInteriorEliminationDataStatus_eq
  variableNoInteriorEliminationDataStatus_eq := variableSource.noInteriorEliminationDataStatus_eq
  regularNoDtnDataStatus_eq := regularSource.noDtnDataStatus_eq
  variableNoDtnDataStatus_eq := variableSource.noDtnDataStatus_eq
  regularNoArithmeticTargetStatus_eq := regularSource.noArithmeticTargetStatus_eq
  variableNoArithmeticTargetStatus_eq := variableSource.noArithmeticTargetStatus_eq
  regularNextPhaseStatus_eq := regularSource.nextPhaseStatus_eq
  variableNextPhaseStatus_eq := variableSource.nextPhaseStatus_eq

end SM3db2fRGeneratedOperationalDegreeReciprocalSourceLedger

end Smoke

end CNNA.PillarA.Arithmetic
