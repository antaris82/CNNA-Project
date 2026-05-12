import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db4aRAccumulatedTraceEvaluationStatus where
  | accumulatedTraceEvaluationFromSM3db3RTrace
  deriving DecidableEq, Repr

inductive SM3db4aRAccumulatedEntryFoldStatus where
  | accumulatedEntryFoldFromTracePivotStepResidualAndOrder
  deriving DecidableEq, Repr

inductive SM3db4aRAccumulatedInverseCandidateEntryStatus where
  | accumulatedInverseCandidateEntryFromAccumulatedTraceEvaluation
  deriving DecidableEq, Repr

inductive SM3db4aRAccumulatedSourceStatus where
  | accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  deriving DecidableEq, Repr

inductive SM3db4aRNotOnlyLocalResidualWrapperStatus where
  | notOnlyLocalResidualWrapper
  deriving DecidableEq, Repr

inductive SM3db4aRFoldUpdateOrderStatus where
  | foldUpdateOrderRecordedFromTraceStepPair
  deriving DecidableEq, Repr

inductive SM3db4aRNextPositivePhase where
  | sm3db5RMatrixExportAfterAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3db4aRGeneratedInteriorAccumulatedEntryLedgerStatus where
  | generatedInteriorAccumulatedEntryClosed
  deriving DecidableEq, Repr

def generatedInteriorTracePivotContribution
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (T.traceStepOf i).pivotDatum.pivotEntry + (T.traceStepOf j).pivotDatum.pivotEntry

def generatedInteriorTraceLocalStepContribution
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (T.traceStepOf i).localStep.stepUpdate.baseEntry i j

def generatedInteriorTraceResidualContribution
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (T.traceStepOf i).residualDatum.rowResidual j

def generatedInteriorTraceFoldUpdateOrderContribution
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (T.traceStepOf j).stepUpdate.columnResidual i

def generatedInteriorAccumulatedEntryValue
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorTracePivotContribution T i j +
    generatedInteriorTraceLocalStepContribution T i j +
      generatedInteriorTraceResidualContribution T i j +
        generatedInteriorTraceFoldUpdateOrderContribution T i j

structure GeneratedInteriorAccumulatedEntryFold
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
  trace : GeneratedInteriorEliminationTrace Cell p A P wp W E K
  baseTraceEvaluation : GeneratedInteriorTraceEvaluation Cell p A P wp W E K T
  pivotContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  localStepContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  residualContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  foldUpdateOrderContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  accumulatedEntry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  foldStatus : SM3db4aRAccumulatedEntryFoldStatus
  sourceStatus : SM3db4aRAccumulatedSourceStatus
  notOnlyLocalResidualWrapperStatus : SM3db4aRNotOnlyLocalResidualWrapperStatus
  foldUpdateOrderStatus : SM3db4aRFoldUpdateOrderStatus
  noMatrixInvStatus : SM3db4RNoMatrixInvStatus
  noFreeInverseEntryTableStatus : SM3db4RNoFreeInverseEntryTableStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noMatrixExportStatus : SM3db4RNoMatrixExportStatus
  noProductProofStatus : SM3db4RNoProductProofStatus
  noTwoSidedInvStatus : SM3db4RNoTwoSidedInvStatus
  trace_is_source : trace = T
  baseTraceEvaluation_is_fromTrace :
    baseTraceEvaluation = GeneratedInteriorTraceEvaluation.fromTrace T
  pivotContribution_from_tracePivotData :
    ∀ i j : GeneratedInteriorIndex A,
      pivotContribution i j = generatedInteriorTracePivotContribution T i j
  localStepContribution_from_traceLocalSteps :
    ∀ i j : GeneratedInteriorIndex A,
      localStepContribution i j = generatedInteriorTraceLocalStepContribution T i j
  residualContribution_from_traceResidualData :
    ∀ i j : GeneratedInteriorIndex A,
      residualContribution i j = generatedInteriorTraceResidualContribution T i j
  foldUpdateOrderContribution_from_traceStepOrder :
    ∀ i j : GeneratedInteriorIndex A,
      foldUpdateOrderContribution i j =
        generatedInteriorTraceFoldUpdateOrderContribution T i j
  accumulatedEntry_from_components :
    ∀ i j : GeneratedInteriorIndex A,
      accumulatedEntry i j =
        pivotContribution i j + localStepContribution i j +
          residualContribution i j + foldUpdateOrderContribution i j
  accumulatedEntry_from_trace :
    ∀ i j : GeneratedInteriorIndex A,
      accumulatedEntry i j = generatedInteriorAccumulatedEntryValue T i j
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  foldStatus_eq :
    foldStatus =
      SM3db4aRAccumulatedEntryFoldStatus.accumulatedEntryFoldFromTracePivotStepResidualAndOrder
  sourceStatus_eq :
    sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  notOnlyLocalResidualWrapperStatus_eq :
    notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  foldUpdateOrderStatus_eq :
    foldUpdateOrderStatus =
      SM3db4aRFoldUpdateOrderStatus.foldUpdateOrderRecordedFromTraceStepPair
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus_eq :
    noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus_eq :
    noProductProofStatus = SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R

namespace GeneratedInteriorAccumulatedEntryFold

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

def fromEliminationTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T where
  trace := T
  baseTraceEvaluation := GeneratedInteriorTraceEvaluation.fromTrace T
  pivotContribution := fun i j => generatedInteriorTracePivotContribution T i j
  localStepContribution := fun i j => generatedInteriorTraceLocalStepContribution T i j
  residualContribution := fun i j => generatedInteriorTraceResidualContribution T i j
  foldUpdateOrderContribution := fun i j =>
    generatedInteriorTraceFoldUpdateOrderContribution T i j
  accumulatedEntry := fun i j => generatedInteriorAccumulatedEntryValue T i j
  foldStatus :=
    SM3db4aRAccumulatedEntryFoldStatus.accumulatedEntryFoldFromTracePivotStepResidualAndOrder
  sourceStatus :=
    SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  notOnlyLocalResidualWrapperStatus :=
    SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  foldUpdateOrderStatus :=
    SM3db4aRFoldUpdateOrderStatus.foldUpdateOrderRecordedFromTraceStepPair
  noMatrixInvStatus := SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus :=
    SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus := SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus := SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus := SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R
  trace_is_source := by
    rfl
  baseTraceEvaluation_is_fromTrace := by
    rfl
  pivotContribution_from_tracePivotData := by
    intro i j
    rfl
  localStepContribution_from_traceLocalSteps := by
    intro i j
    rfl
  residualContribution_from_traceResidualData := by
    intro i j
    rfl
  foldUpdateOrderContribution_from_traceStepOrder := by
    intro i j
    rfl
  accumulatedEntry_from_components := by
    intro i j
    rfl
  accumulatedEntry_from_trace := by
    intro i j
    rfl
  trace_source_eq_SM3db3R :=
    T.sourceStatus_eq
  foldStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  notOnlyLocalResidualWrapperStatus_eq := by
    rfl
  foldUpdateOrderStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noFreeInverseEntryTableStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl
  noProductProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl

end GeneratedInteriorAccumulatedEntryFold

structure GeneratedInteriorAccumulatedTraceEvaluation
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
  trace : GeneratedInteriorEliminationTrace Cell p A P wp W E K
  accumulatedEntryFold : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  entry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  evaluationStatus : SM3db4aRAccumulatedTraceEvaluationStatus
  sourceStatus : SM3db4aRAccumulatedSourceStatus
  noMatrixInvStatus : SM3db4RNoMatrixInvStatus
  noFreeInverseEntryTableStatus : SM3db4RNoFreeInverseEntryTableStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noMatrixExportStatus : SM3db4RNoMatrixExportStatus
  noProductProofStatus : SM3db4RNoProductProofStatus
  noTwoSidedInvStatus : SM3db4RNoTwoSidedInvStatus
  trace_is_source : trace = T
  accumulatedEntryFold_is_fromTrace :
    accumulatedEntryFold = GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T
  entry_eq_accumulatedFold :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = accumulatedEntryFold.accumulatedEntry i j
  entry_eq_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = generatedInteriorAccumulatedEntryValue T i j
  evaluationStatus_eq :
    evaluationStatus =
      SM3db4aRAccumulatedTraceEvaluationStatus.accumulatedTraceEvaluationFromSM3db3RTrace
  sourceStatus_eq :
    sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus_eq :
    noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus_eq :
    noProductProofStatus = SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R

namespace GeneratedInteriorAccumulatedTraceEvaluation

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

def fromEliminationTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorAccumulatedTraceEvaluation Cell p A P wp W E K T where
  trace := T
  accumulatedEntryFold := GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T
  entry := fun i j =>
    (GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T).accumulatedEntry i j
  evaluationStatus :=
    SM3db4aRAccumulatedTraceEvaluationStatus.accumulatedTraceEvaluationFromSM3db3RTrace
  sourceStatus :=
    SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  noMatrixInvStatus := SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus :=
    SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus := SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus := SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus := SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R
  trace_is_source := by
    rfl
  accumulatedEntryFold_is_fromTrace := by
    rfl
  entry_eq_accumulatedFold := by
    intro i j
    rfl
  entry_eq_accumulatedTraceValue := by
    intro i j
    rfl
  evaluationStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noFreeInverseEntryTableStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl
  noProductProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl

end GeneratedInteriorAccumulatedTraceEvaluation

structure GeneratedInteriorAccumulatedInverseCandidateEntry
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
  trace : GeneratedInteriorEliminationTrace Cell p A P wp W E K
  accumulatedTraceEvaluation :
    GeneratedInteriorAccumulatedTraceEvaluation Cell p A P wp W E K T
  entry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  candidateStatus : SM3db4aRAccumulatedInverseCandidateEntryStatus
  sourceStatus : SM3db4aRAccumulatedSourceStatus
  notOnlyLocalResidualWrapperStatus : SM3db4aRNotOnlyLocalResidualWrapperStatus
  noMatrixInvStatus : SM3db4RNoMatrixInvStatus
  noFreeInverseEntryTableStatus : SM3db4RNoFreeInverseEntryTableStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noMatrixExportStatus : SM3db4RNoMatrixExportStatus
  noProductProofStatus : SM3db4RNoProductProofStatus
  noTwoSidedInvStatus : SM3db4RNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus :
    SM3db4RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db4RNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4RNoArithmeticTargetStatus
  nextPositivePhase : SM3db4aRNextPositivePhase
  trace_is_source : trace = T
  accumulatedTraceEvaluation_is_fromTrace :
    accumulatedTraceEvaluation =
      GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T
  entry_eq_accumulatedTraceEvaluation :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = accumulatedTraceEvaluation.entry i j
  entry_eq_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = generatedInteriorAccumulatedEntryValue T i j
  source_is_accumulatedTraceEvaluation :
    sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  candidateStatus_eq :
    candidateStatus =
      SM3db4aRAccumulatedInverseCandidateEntryStatus.accumulatedInverseCandidateEntryFromAccumulatedTraceEvaluation
  notOnlyLocalResidualWrapperStatus_eq :
    notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus_eq :
    noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus_eq :
    noProductProofStatus = SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3db4RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db4R
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db4RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4R
  nextPositivePhase_eq :
    nextPositivePhase = SM3db4aRNextPositivePhase.sm3db5RMatrixExportAfterAccumulatedEntry

namespace GeneratedInteriorAccumulatedInverseCandidateEntry

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

def fromAccumulatedTraceEvaluation
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T where
  trace := T
  accumulatedTraceEvaluation :=
    GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T
  entry := fun i j =>
    (GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T).entry i j
  candidateStatus :=
    SM3db4aRAccumulatedInverseCandidateEntryStatus.accumulatedInverseCandidateEntryFromAccumulatedTraceEvaluation
  sourceStatus :=
    SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  notOnlyLocalResidualWrapperStatus :=
    SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  noMatrixInvStatus := SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus :=
    SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus := SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus := SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus := SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R
  noInteriorEliminationCertificateStatus :=
    SM3db4RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db4R
  noInteriorEliminationDataStatus :=
    SM3db4RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4R
  noDtnDataStatus :=
    SM3db4RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4R
  noArithmeticTargetStatus :=
    SM3db4RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4R
  nextPositivePhase := SM3db4aRNextPositivePhase.sm3db5RMatrixExportAfterAccumulatedEntry
  trace_is_source := by
    rfl
  accumulatedTraceEvaluation_is_fromTrace := by
    rfl
  entry_eq_accumulatedTraceEvaluation := by
    intro i j
    rfl
  entry_eq_accumulatedTraceValue := by
    intro i j
    rfl
  source_is_accumulatedTraceEvaluation := by
    rfl
  candidateStatus_eq := by
    rfl
  notOnlyLocalResidualWrapperStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noFreeInverseEntryTableStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl
  noProductProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPositivePhase_eq := by
    rfl

end GeneratedInteriorAccumulatedInverseCandidateEntry

def accumulatedEntry_from_eliminationTrace
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T :=
  GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T

def accumulatedTraceEvaluation_from_eliminationTrace
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorAccumulatedTraceEvaluation Cell p A P wp W E K T :=
  GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T

def accumulatedInverseCandidateEntry_from_eliminationTrace
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T :=
  GeneratedInteriorAccumulatedInverseCandidateEntry.fromAccumulatedTraceEvaluation T

theorem accumulatedEntry_uses_pivotData
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    F.pivotContribution i j = generatedInteriorTracePivotContribution T i j :=
  F.pivotContribution_from_tracePivotData i j

theorem accumulatedEntry_uses_localSteps
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    F.localStepContribution i j = generatedInteriorTraceLocalStepContribution T i j :=
  F.localStepContribution_from_traceLocalSteps i j

theorem accumulatedEntry_uses_residualData
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    F.residualContribution i j = generatedInteriorTraceResidualContribution T i j :=
  F.residualContribution_from_traceResidualData i j

theorem accumulatedEntry_respects_foldUpdateOrder
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    F.foldUpdateOrderContribution i j =
      generatedInteriorTraceFoldUpdateOrderContribution T i j :=
  F.foldUpdateOrderContribution_from_traceStepOrder i j

theorem accumulatedEntry_from_components
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    F.accumulatedEntry i j =
      F.pivotContribution i j + F.localStepContribution i j +
        F.residualContribution i j + F.foldUpdateOrderContribution i j :=
  F.accumulatedEntry_from_components i j

theorem inverseCandidateEntry_source_is_accumulatedTraceEvaluation
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
    (I : GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T) :
    I.accumulatedTraceEvaluation =
      GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T :=
  I.accumulatedTraceEvaluation_is_fromTrace

theorem sm3db4R_not_only_localResidualWrapper
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T) :
    F.notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper :=
  F.notOnlyLocalResidualWrapperStatus_eq

theorem noFreeEntryTable_for_accumulatedEntryFold
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T) :
    F.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable :=
  F.noFreeInverseEntryTableStatus_eq

theorem noExternalInverseOracle_for_accumulatedEntryFold
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
    (F : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T) :
    F.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry :=
  F.noExternalInverseOracleStatus_eq

def regularGeneratedInteriorAccumulatedEntryFold
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorAccumulatedEntryFold
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp) :=
  accumulatedEntry_from_eliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableGeneratedInteriorAccumulatedEntryFold
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorAccumulatedEntryFold
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp) :=
  accumulatedEntry_from_eliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularGeneratedInteriorAccumulatedTraceEvaluation
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorAccumulatedTraceEvaluation
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp) :=
  accumulatedTraceEvaluation_from_eliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableGeneratedInteriorAccumulatedTraceEvaluation
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorAccumulatedTraceEvaluation
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp) :=
  accumulatedTraceEvaluation_from_eliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularGeneratedInteriorAccumulatedInverseCandidateEntry
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorAccumulatedInverseCandidateEntry
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp) :=
  accumulatedInverseCandidateEntry_from_eliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableGeneratedInteriorAccumulatedInverseCandidateEntry
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorAccumulatedInverseCandidateEntry
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp) :=
  accumulatedInverseCandidateEntry_from_eliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3db4aRGeneratedInteriorAccumulatedEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3db4aRGeneratedInteriorAccumulatedEntryLedgerStatus
  sm3db4Ledger :
    SM3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularAccumulatedFold :
    GeneratedInteriorAccumulatedEntryFold
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
  variableAccumulatedFold :
    GeneratedInteriorAccumulatedEntryFold
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
  regularAccumulatedInverseCandidateEntry :
    GeneratedInteriorAccumulatedInverseCandidateEntry
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
  variableAccumulatedInverseCandidateEntry :
    GeneratedInteriorAccumulatedInverseCandidateEntry
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
  sm3db4Ledger_eq_main :
    sm3db4Ledger =
      sm3db4RGeneratedInteriorInverseCandidateEntryLedger
        b β p regularWeight variableWeight regularPivot variablePivot
  regularFoldNoFreeEntryTable :
    regularAccumulatedFold.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  variableFoldNoFreeEntryTable :
    variableAccumulatedFold.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  regularFoldNoExternalInverseOracle :
    regularAccumulatedFold.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  variableFoldNoExternalInverseOracle :
    variableAccumulatedFold.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  regularCandidateNoMatrixExport :
    regularAccumulatedInverseCandidateEntry.noMatrixExportStatus =
      SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  variableCandidateNoMatrixExport :
    variableAccumulatedInverseCandidateEntry.noMatrixExportStatus =
      SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  regularCandidateNoProductProof :
    regularAccumulatedInverseCandidateEntry.noProductProofStatus =
      SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  variableCandidateNoProductProof :
    variableAccumulatedInverseCandidateEntry.noProductProofStatus =
      SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  regularNextPositivePhase :
    regularAccumulatedInverseCandidateEntry.nextPositivePhase =
      SM3db4aRNextPositivePhase.sm3db5RMatrixExportAfterAccumulatedEntry
  variableNextPositivePhase :
    variableAccumulatedInverseCandidateEntry.nextPositivePhase =
      SM3db4aRNextPositivePhase.sm3db5RMatrixExportAfterAccumulatedEntry
  status_eq_closed :
    status =
      SM3db4aRGeneratedInteriorAccumulatedEntryLedgerStatus.generatedInteriorAccumulatedEntryClosed

def sm3db4aRGeneratedInteriorAccumulatedEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3db4aRGeneratedInteriorAccumulatedEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status :=
    SM3db4aRGeneratedInteriorAccumulatedEntryLedgerStatus.generatedInteriorAccumulatedEntryClosed
  sm3db4Ledger :=
    sm3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularAccumulatedFold :=
    regularGeneratedInteriorAccumulatedEntryFold b p regularWeight
  variableAccumulatedFold :=
    variableGeneratedInteriorAccumulatedEntryFold β p variableWeight
  regularAccumulatedInverseCandidateEntry :=
    regularGeneratedInteriorAccumulatedInverseCandidateEntry b p regularWeight
  variableAccumulatedInverseCandidateEntry :=
    variableGeneratedInteriorAccumulatedInverseCandidateEntry β p variableWeight
  sm3db4Ledger_eq_main := by
    rfl
  regularFoldNoFreeEntryTable := by
    rfl
  variableFoldNoFreeEntryTable := by
    rfl
  regularFoldNoExternalInverseOracle := by
    rfl
  variableFoldNoExternalInverseOracle := by
    rfl
  regularCandidateNoMatrixExport := by
    rfl
  variableCandidateNoMatrixExport := by
    rfl
  regularCandidateNoProductProof := by
    rfl
  variableCandidateNoProductProof := by
    rfl
  regularNextPositivePhase := by
    rfl
  variableNextPositivePhase := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3db4aRGeneratedInteriorAccumulatedEntryLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db4aRGeneratedInteriorAccumulatedEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3db4aRGeneratedInteriorAccumulatedEntryLedgerStatus.generatedInteriorAccumulatedEntryClosed := by
  rfl

theorem sm3db4aRGeneratedInteriorAccumulatedEntryLedger_regularNextPositivePhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db4aRGeneratedInteriorAccumulatedEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularAccumulatedInverseCandidateEntry.nextPositivePhase =
      SM3db4aRNextPositivePhase.sm3db5RMatrixExportAfterAccumulatedEntry := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
