import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db3aRTracePivotTerminalCoverageStatus where
  | tracePivotTerminalCoverageFromSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3aRTerminalFoldResidualCoverageRequirementStatus where
  | terminalFoldResidualCoverageRequiredFromSM3db4aR
  deriving DecidableEq, Repr

inductive SM3db3aRTerminalCoverageExportStatus where
  | terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db3aRNoAccumulatedEntryCancellationStatus where
  | noAccumulatedEntryCancellationInvariantInTracePivotTerminalCoverage
  deriving DecidableEq, Repr

inductive SM3db3aRNoProductIdentityProofStatus where
  | noProductIdentityProofInTracePivotTerminalCoverage
  deriving DecidableEq, Repr

inductive SM3db3aRNoTwoSidedInvStatus where
  | noTwoSidedInvInTracePivotTerminalCoverage
  deriving DecidableEq, Repr

inductive SM3db3aRNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInTracePivotTerminalCoverage
  deriving DecidableEq, Repr

inductive SM3db3aRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db3aR
  deriving DecidableEq, Repr

inductive SM3db3aRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db3aR
  deriving DecidableEq, Repr

inductive SM3db3aRNextPhaseStatus where
  | sm3db4aTTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db3aRTracePivotTerminalCoverageLedgerStatus where
  | tracePivotTerminalCoverageSourceAudited
  deriving DecidableEq, Repr

structure GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR
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
  traceIndexCarrier : Finset (GeneratedInteriorIndex A)
  localStepOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationStep Cell p A P wp W E K
  traceStepOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationTraceStep Cell p A P wp W E K (localStepOf i)
  pivotOf : GeneratedInteriorIndex A → GeneratedInteriorIndex A
  coverageStatus : SM3db3aRTracePivotTerminalCoverageStatus
  sourceStatus : SM3db3RTraceSourceStatus
  noExternalTraceOracleStatus : SM3db3RNoExternalTraceOracleStatus
  noExternalOrderOracleStatus : SM3db3RNoExternalOrderOracleStatus
  noFreePivotListStatus : SM3db3RNoFreePivotListStatus
  noProductIdentityProofStatus : SM3db3aRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db3aRNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db3aRNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db3aRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db3aRNoArithmeticTargetStatus
  trace_eq : trace = T
  traceIndexCarrier_eq_trace : traceIndexCarrier = T.traceIndexCarrier
  traceIndexCarrier_eq_carrierIndexCarrier : traceIndexCarrier = K.indexCarrier
  localStepOf_eq_trace : ∀ i : GeneratedInteriorIndex A, localStepOf i = T.localStepOf i
  traceStepOf_localStep_eq :
    ∀ i : GeneratedInteriorIndex A, (traceStepOf i).localStep = localStepOf i
  pivotOf_eq_traceStepPivotIndex :
    ∀ i : GeneratedInteriorIndex A, pivotOf i = (traceStepOf i).pivotIndex
  pivotOf_eq_localStepPivotIndex :
    ∀ i : GeneratedInteriorIndex A, pivotOf i = (localStepOf i).pivotDatum.pivotIndex
  localStepOf_eq_SM3db2R_step :
    ∀ i : GeneratedInteriorIndex A,
      localStepOf i = localStep_from_SM3db1R_node K i
  pivot_bound_to_SM3db1R_node :
    ∀ i : GeneratedInteriorIndex A,
      (localStepOf i).pivotDatum.node = K.nodeOf (localStepOf i).pivotDatum.pivotIndex
  rowResidual_eq_SM3cR_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      (localStepOf i).residualDatum.rowResidual j =
        generatedInteriorLocalRowResidual W (localStepOf i).pivotDatum.pivotIndex j
  columnResidual_eq_SM3cR_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      (localStepOf i).residualDatum.columnResidual j =
        generatedInteriorLocalColumnResidual W (localStepOf i).pivotDatum.pivotIndex j
  sourceStatus_eq :
    sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  coverageStatus_eq :
    coverageStatus =
      SM3db3aRTracePivotTerminalCoverageStatus.tracePivotTerminalCoverageFromSM3db3R
  noExternalTraceOracleStatus_eq :
    noExternalTraceOracleStatus = SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  noExternalOrderOracleStatus_eq :
    noExternalOrderOracleStatus = SM3db3RNoExternalOrderOracleStatus.noExternalOrderOracle
  noFreePivotListStatus_eq :
    noFreePivotListStatus = SM3db3RNoFreePivotListStatus.noFreePivotList
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db3aRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotTerminalCoverage
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db3aRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotTerminalCoverage
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db3aRNoInteriorEliminationDataStatus.noInteriorEliminationDataInTracePivotTerminalCoverage
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db3aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db3aR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db3aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db3aR

namespace GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR

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

def fromTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T where
  trace := T
  traceIndexCarrier := T.traceIndexCarrier
  localStepOf := T.localStepOf
  traceStepOf := T.traceStepOf
  pivotOf := fun i => (T.traceStepOf i).pivotIndex
  coverageStatus :=
    SM3db3aRTracePivotTerminalCoverageStatus.tracePivotTerminalCoverageFromSM3db3R
  sourceStatus := T.sourceStatus
  noExternalTraceOracleStatus := T.noExternalTraceOracleStatus
  noExternalOrderOracleStatus := T.noExternalOrderOracleStatus
  noFreePivotListStatus := T.noFreePivotListStatus
  noProductIdentityProofStatus :=
    SM3db3aRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotTerminalCoverage
  noTwoSidedInvStatus :=
    SM3db3aRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotTerminalCoverage
  noInteriorEliminationDataStatus :=
    SM3db3aRNoInteriorEliminationDataStatus.noInteriorEliminationDataInTracePivotTerminalCoverage
  noDtnDataStatus :=
    SM3db3aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db3aR
  noArithmeticTargetStatus :=
    SM3db3aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db3aR
  trace_eq := by
    rfl
  traceIndexCarrier_eq_trace := by
    rfl
  traceIndexCarrier_eq_carrierIndexCarrier :=
    T.traceIndexCarrier_eq_carrierIndexCarrier
  localStepOf_eq_trace := by
    intro i
    rfl
  traceStepOf_localStep_eq :=
    T.traceStep_localStep_eq_SM3db2R_step
  pivotOf_eq_traceStepPivotIndex := by
    intro i
    rfl
  pivotOf_eq_localStepPivotIndex := by
    intro i
    exact (T.traceStepOf i).pivotIndex_eq_localStepPivotIndex
  localStepOf_eq_SM3db2R_step :=
    T.localStepOf_eq_SM3db2R_step
  pivot_bound_to_SM3db1R_node :=
    T.traceStep_pivot_bound_to_SM3db1R_node
  rowResidual_eq_SM3cR_interiorBlock :=
    T.traceStep_residual_eq_SM3cR_interiorBlock
  columnResidual_eq_SM3cR_interiorBlock :=
    T.traceStep_columnResidual_eq_SM3cR_interiorBlock
  sourceStatus_eq :=
    T.sourceStatus_eq
  coverageStatus_eq := by
    rfl
  noExternalTraceOracleStatus_eq :=
    T.noExternalTraceOracleStatus_eq
  noExternalOrderOracleStatus_eq :=
    T.noExternalOrderOracleStatus_eq
  noFreePivotListStatus_eq :=
    T.noFreePivotListStatus_eq
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

theorem pivotCoverage_source_eq_SM3db3R
    (C : GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T) :
    C.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps :=
  C.sourceStatus_eq

theorem pivotCoverage_noTwoSidedInv
    (C : GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T) :
    C.noTwoSidedInvStatus =
      SM3db3aRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotTerminalCoverage :=
  C.noTwoSidedInvStatus_eq

end GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR

structure GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR
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
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  tracePivotCoverage :
    GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T
  accumulatedTraceEvaluation : GeneratedInteriorAccumulatedTraceEvaluation Cell p A P wp W E K T
  accumulatedEntryFold : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  requirementStatus : SM3db3aRTerminalFoldResidualCoverageRequirementStatus
  exportStatus : SM3db3aRTerminalCoverageExportStatus
  noAccumulatedEntryCancellationStatus : SM3db3aRNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3db3aRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db3aRNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db3aRNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db3aRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db3aRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db3aRNextPhaseStatus
  invarianceStatus_eq :
    invariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  tracePivotCoverage_source_eq_SM3db3R :
    tracePivotCoverage.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceEvaluation_eq_invariance :
    accumulatedTraceEvaluation = invariance.blockFoldNormalForm.accumulatedTraceEvaluation
  accumulatedEntryFold_eq_invariance :
    accumulatedEntryFold = invariance.blockFoldNormalForm.accumulatedEntryFold
  accumulatedTraceSource_eq_SM3db4aR :
    accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  requirementStatus_eq :
    requirementStatus =
      SM3db3aRTerminalFoldResidualCoverageRequirementStatus.terminalFoldResidualCoverageRequiredFromSM3db4aR
  exportStatus_eq :
    exportStatus =
      SM3db3aRTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3db3aRNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTracePivotTerminalCoverage
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db3aRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotTerminalCoverage
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db3aRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotTerminalCoverage
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db3aRNoInteriorEliminationDataStatus.noInteriorEliminationDataInTracePivotTerminalCoverage
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db3aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db3aR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db3aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db3aR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage

namespace GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR

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

def fromInvariance
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR Cell p A P wp W E K T where
  invariance := I
  tracePivotCoverage :=
    GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR.fromTrace T
  accumulatedTraceEvaluation := I.blockFoldNormalForm.accumulatedTraceEvaluation
  accumulatedEntryFold := I.blockFoldNormalForm.accumulatedEntryFold
  requirementStatus :=
    SM3db3aRTerminalFoldResidualCoverageRequirementStatus.terminalFoldResidualCoverageRequiredFromSM3db4aR
  exportStatus :=
    SM3db3aRTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  noAccumulatedEntryCancellationStatus :=
    SM3db3aRNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTracePivotTerminalCoverage
  noProductIdentityProofStatus :=
    SM3db3aRNoProductIdentityProofStatus.noProductIdentityProofInTracePivotTerminalCoverage
  noTwoSidedInvStatus :=
    SM3db3aRNoTwoSidedInvStatus.noTwoSidedInvInTracePivotTerminalCoverage
  noInteriorEliminationDataStatus :=
    SM3db3aRNoInteriorEliminationDataStatus.noInteriorEliminationDataInTracePivotTerminalCoverage
  noDtnDataStatus :=
    SM3db3aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db3aR
  noArithmeticTargetStatus :=
    SM3db3aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db3aR
  nextPhaseStatus := SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage
  invarianceStatus_eq :=
    I.invarianceStatus_eq
  tracePivotCoverage_source_eq_SM3db3R :=
    (GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR.fromTrace T).sourceStatus_eq
  accumulatedTraceEvaluation_eq_invariance := by
    rfl
  accumulatedEntryFold_eq_invariance := by
    rfl
  accumulatedTraceSource_eq_SM3db4aR :=
    I.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    I.accumulatedFoldSource_eq_SM3db4aR
  requirementStatus_eq := by
    rfl
  exportStatus_eq := by
    rfl
  noAccumulatedEntryCancellationStatus_eq := by
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

theorem nextPhase_is_SM3db4aT
    (R : GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR Cell p A P wp W E K T) :
    R.nextPhaseStatus = SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage :=
  R.nextPhaseStatus_eq

end GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR

structure GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR
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
  requirement : GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR Cell p A P wp W E K T
  auditStatus : SM3db3aRTracePivotTerminalCoverageLedgerStatus
  terminalCoverageExportStatus : SM3db3aRTerminalCoverageExportStatus
  nextPhaseStatus : SM3db3aRNextPhaseStatus
  tracePivotCoverageStatus_eq :
    requirement.tracePivotCoverage.coverageStatus =
      SM3db3aRTracePivotTerminalCoverageStatus.tracePivotTerminalCoverageFromSM3db3R
  terminalRequirementStatus_eq :
    requirement.requirementStatus =
      SM3db3aRTerminalFoldResidualCoverageRequirementStatus.terminalFoldResidualCoverageRequiredFromSM3db4aR
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db3aRTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  auditStatus_eq :
    auditStatus = SM3db3aRTracePivotTerminalCoverageLedgerStatus.tracePivotTerminalCoverageSourceAudited
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage

namespace GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR

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

def fromInvariance
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR Cell p A P wp W E K T where
  requirement :=
    GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR.fromInvariance I
  auditStatus := SM3db3aRTracePivotTerminalCoverageLedgerStatus.tracePivotTerminalCoverageSourceAudited
  terminalCoverageExportStatus :=
    SM3db3aRTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  nextPhaseStatus := SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage
  tracePivotCoverageStatus_eq := by
    rfl
  terminalRequirementStatus_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
    rfl
  auditStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR

abbrev RegularGeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularTracePivotTerminalCoverageSourceSM3db3aR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    RegularGeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR b p wp :=
  GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR.fromTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableTracePivotTerminalCoverageSourceSM3db3aR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    VariableGeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR β p wp :=
  GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR.fromTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularTracePivotTerminalCoverageAuditSM3db3aR
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (I : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p wp) :
    RegularGeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR b p wp :=
  GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR.fromInvariance I

def variableTracePivotTerminalCoverageAuditSM3db3aR
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (I : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p wp) :
    VariableGeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR β p wp :=
  GeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR.fromInvariance I

structure SM3db3aRTracePivotTerminalCoverageSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAudit : RegularGeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR b p regularWeight
  variableAudit : VariableGeneratedInteriorTracePivotTerminalCoverageAuditSM3db3aR β p variableWeight
  status : SM3db3aRTracePivotTerminalCoverageLedgerStatus
  terminalCoverageExportStatus : SM3db3aRTerminalCoverageExportStatus
  nextPhaseStatus : SM3db3aRNextPhaseStatus
  regularNextPhaseStatus_eq :
    regularAudit.nextPhaseStatus = SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage
  variableNextPhaseStatus_eq :
    variableAudit.nextPhaseStatus = SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage
  status_eq :
    status = SM3db3aRTracePivotTerminalCoverageLedgerStatus.tracePivotTerminalCoverageSourceAudited
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db3aRTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage

namespace SM3db3aRTracePivotTerminalCoverageSourceLedger

def fromRegularAndVariableInvariance
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularInvariance : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p regularWeight)
    (variableInvariance : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p variableWeight) :
    SM3db3aRTracePivotTerminalCoverageSourceLedger b β p regularWeight variableWeight where
  regularAudit := regularTracePivotTerminalCoverageAuditSM3db3aR regularInvariance
  variableAudit := variableTracePivotTerminalCoverageAuditSM3db3aR variableInvariance
  status := SM3db3aRTracePivotTerminalCoverageLedgerStatus.tracePivotTerminalCoverageSourceAudited
  terminalCoverageExportStatus :=
    SM3db3aRTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilSM3db4aRTerminalResidualCoverage
  nextPhaseStatus := SM3db3aRNextPhaseStatus.sm3db4aTTerminalFoldResidualCoverage
  regularNextPhaseStatus_eq := by
    rfl
  variableNextPhaseStatus_eq := by
    rfl
  status_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3db3aRTracePivotTerminalCoverageSourceLedger

end Smoke

end CNNA.PillarA.Arithmetic
