import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db4aTTerminalFoldStateStatus where
  | terminalFoldStateFromAccumulatedEntryFold
  deriving DecidableEq, Repr

inductive SM3db4aTTerminalResidualCoverageStatus where
  | terminalResidualCoverageFromAccumulatedResidualAndFoldOrder
  deriving DecidableEq, Repr

inductive SM3db4aTTerminalCoverageExportStatus where
  | terminalCoverageSourceBlockedUntilTerminalIdentityFields
  deriving DecidableEq, Repr

inductive SM3db4aTTerminalIdentityFieldStatus where
  | terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  deriving DecidableEq, Repr

inductive SM3db4aTNoAccumulatedEntryCancellationStatus where
  | noAccumulatedEntryCancellationInvariantInTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db4aTNoProductIdentityProofStatus where
  | noProductIdentityProofInTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db4aTNoTwoSidedInvStatus where
  | noTwoSidedInvInTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db4aTNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db4aTNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db4aTNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3db4aTNextPhaseStatus where
  | sm3db4aUExposeTerminalFoldResidualIdentityFields
  deriving DecidableEq, Repr

inductive SM3db4aTLedgerStatus where
  | terminalFoldResidualCoverageAuditClosed
  deriving DecidableEq, Repr

structure GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT
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
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  accumulatedTraceEvaluation : GeneratedInteriorAccumulatedTraceEvaluation Cell p A P wp W E K T
  accumulatedEntryFold : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  terminalFoldState : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  terminalResidualContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  terminalFoldUpdateOrderContribution : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  terminalFoldStateStatus : SM3db4aTTerminalFoldStateStatus
  terminalResidualCoverageStatus : SM3db4aTTerminalResidualCoverageStatus
  leftTerminalIdentityFieldStatus : SM3db4aTTerminalIdentityFieldStatus
  rightTerminalIdentityFieldStatus : SM3db4aTTerminalIdentityFieldStatus
  terminalCoverageExportStatus : SM3db4aTTerminalCoverageExportStatus
  noAccumulatedEntryCancellationStatus : SM3db4aTNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3db4aTNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db4aTNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db4aTNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4aTNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4aTNoArithmeticTargetStatus
  nextPhaseStatus : SM3db4aTNextPhaseStatus
  invariance_eq_requirement : invariance = requirement.invariance
  accumulatedTraceEvaluation_eq_requirement :
    accumulatedTraceEvaluation = requirement.accumulatedTraceEvaluation
  accumulatedEntryFold_eq_requirement :
    accumulatedEntryFold = requirement.accumulatedEntryFold
  terminalFoldState_eq_accumulatedEntryFold : terminalFoldState = accumulatedEntryFold
  terminalResidualContribution_eq_accumulatedFold :
    ∀ i j : GeneratedInteriorIndex A,
      terminalResidualContribution i j = accumulatedEntryFold.residualContribution i j
  terminalResidualContribution_eq_trace :
    ∀ i j : GeneratedInteriorIndex A,
      terminalResidualContribution i j = generatedInteriorTraceResidualContribution T i j
  terminalFoldUpdateOrderContribution_eq_accumulatedFold :
    ∀ i j : GeneratedInteriorIndex A,
      terminalFoldUpdateOrderContribution i j =
        accumulatedEntryFold.foldUpdateOrderContribution i j
  terminalFoldUpdateOrderContribution_eq_trace :
    ∀ i j : GeneratedInteriorIndex A,
      terminalFoldUpdateOrderContribution i j =
        generatedInteriorTraceFoldUpdateOrderContribution T i j
  invarianceStatus_eq :
    invariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  requirementStatus_eq :
    requirement.requirementStatus =
      SM3db3aRTerminalFoldResidualCoverageRequirementStatus.terminalFoldResidualCoverageRequiredFromSM3db4aR
  tracePivotCoverage_source_eq_SM3db3R :
    requirement.tracePivotCoverage.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  terminalFoldStateSource_eq_SM3db4aR :
    terminalFoldState.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  terminalFoldStateFoldStatus_eq :
    terminalFoldState.foldStatus =
      SM3db4aRAccumulatedEntryFoldStatus.accumulatedEntryFoldFromTracePivotStepResidualAndOrder
  terminalFoldStateFoldUpdateOrderStatus_eq :
    terminalFoldState.foldUpdateOrderStatus =
      SM3db4aRFoldUpdateOrderStatus.foldUpdateOrderRecordedFromTraceStepPair
  terminalFoldStateStatus_eq :
    terminalFoldStateStatus =
      SM3db4aTTerminalFoldStateStatus.terminalFoldStateFromAccumulatedEntryFold
  terminalResidualCoverageStatus_eq :
    terminalResidualCoverageStatus =
      SM3db4aTTerminalResidualCoverageStatus.terminalResidualCoverageFromAccumulatedResidualAndFoldOrder
  leftTerminalIdentityFieldStatus_eq :
    leftTerminalIdentityFieldStatus =
      SM3db4aTTerminalIdentityFieldStatus.terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  rightTerminalIdentityFieldStatus_eq :
    rightTerminalIdentityFieldStatus =
      SM3db4aTTerminalIdentityFieldStatus.terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3db4aTNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalFoldResidualCoverage
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db4aTNoProductIdentityProofStatus.noProductIdentityProofInTerminalFoldResidualCoverage
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4aTNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualCoverage
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4aTNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalFoldResidualCoverage
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db4aTNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalFoldResidualCoverage
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4aTNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalFoldResidualCoverage
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aTNextPhaseStatus.sm3db4aUExposeTerminalFoldResidualIdentityFields

namespace GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT

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
    (R : GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T where
  requirement := R
  invariance := R.invariance
  accumulatedTraceEvaluation := R.accumulatedTraceEvaluation
  accumulatedEntryFold := R.accumulatedEntryFold
  terminalFoldState := R.accumulatedEntryFold
  terminalResidualContribution := R.accumulatedEntryFold.residualContribution
  terminalFoldUpdateOrderContribution := R.accumulatedEntryFold.foldUpdateOrderContribution
  terminalFoldStateStatus :=
    SM3db4aTTerminalFoldStateStatus.terminalFoldStateFromAccumulatedEntryFold
  terminalResidualCoverageStatus :=
    SM3db4aTTerminalResidualCoverageStatus.terminalResidualCoverageFromAccumulatedResidualAndFoldOrder
  leftTerminalIdentityFieldStatus :=
    SM3db4aTTerminalIdentityFieldStatus.terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  rightTerminalIdentityFieldStatus :=
    SM3db4aTTerminalIdentityFieldStatus.terminalIdentityFieldMissingFromCurrentSM3db4aRAPI
  terminalCoverageExportStatus :=
    SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  noAccumulatedEntryCancellationStatus :=
    SM3db4aTNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalFoldResidualCoverage
  noProductIdentityProofStatus :=
    SM3db4aTNoProductIdentityProofStatus.noProductIdentityProofInTerminalFoldResidualCoverage
  noTwoSidedInvStatus :=
    SM3db4aTNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualCoverage
  noInteriorEliminationDataStatus :=
    SM3db4aTNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalFoldResidualCoverage
  noDtnDataStatus :=
    SM3db4aTNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalFoldResidualCoverage
  noArithmeticTargetStatus :=
    SM3db4aTNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalFoldResidualCoverage
  nextPhaseStatus :=
    SM3db4aTNextPhaseStatus.sm3db4aUExposeTerminalFoldResidualIdentityFields
  invariance_eq_requirement := by
    rfl
  accumulatedTraceEvaluation_eq_requirement := by
    rfl
  accumulatedEntryFold_eq_requirement := by
    rfl
  terminalFoldState_eq_accumulatedEntryFold := by
    rfl
  terminalResidualContribution_eq_accumulatedFold := by
    intro i j
    rfl
  terminalResidualContribution_eq_trace := by
    intro i j
    exact R.accumulatedEntryFold.residualContribution_from_traceResidualData i j
  terminalFoldUpdateOrderContribution_eq_accumulatedFold := by
    intro i j
    rfl
  terminalFoldUpdateOrderContribution_eq_trace := by
    intro i j
    exact R.accumulatedEntryFold.foldUpdateOrderContribution_from_traceStepOrder i j
  invarianceStatus_eq :=
    R.invarianceStatus_eq
  requirementStatus_eq :=
    R.requirementStatus_eq
  tracePivotCoverage_source_eq_SM3db3R :=
    R.tracePivotCoverage_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    R.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    R.accumulatedFoldSource_eq_SM3db4aR
  terminalFoldStateSource_eq_SM3db4aR :=
    R.accumulatedFoldSource_eq_SM3db4aR
  terminalFoldStateFoldStatus_eq :=
    R.accumulatedEntryFold.foldStatus_eq
  terminalFoldStateFoldUpdateOrderStatus_eq :=
    R.accumulatedEntryFold.foldUpdateOrderStatus_eq
  terminalFoldStateStatus_eq := by
    rfl
  terminalResidualCoverageStatus_eq := by
    rfl
  leftTerminalIdentityFieldStatus_eq := by
    rfl
  rightTerminalIdentityFieldStatus_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
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

def fromInvariance
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T :=
  fromRequirement (GeneratedInteriorTerminalFoldResidualCoverageRequirementSM3db3aR.fromInvariance I)

theorem terminalResidualContribution_from_trace
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    C.terminalResidualContribution i j = generatedInteriorTraceResidualContribution T i j :=
  C.terminalResidualContribution_eq_trace i j

theorem terminalFoldUpdateOrderContribution_from_trace
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    C.terminalFoldUpdateOrderContribution i j =
      generatedInteriorTraceFoldUpdateOrderContribution T i j :=
  C.terminalFoldUpdateOrderContribution_eq_trace i j

theorem terminalCoverageSource_still_blocked
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T) :
    C.terminalCoverageExportStatus =
      SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields :=
  C.terminalCoverageExportStatus_eq

theorem noProductIdentityProof
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T) :
    C.noProductIdentityProofStatus =
      SM3db4aTNoProductIdentityProofStatus.noProductIdentityProofInTerminalFoldResidualCoverage :=
  C.noProductIdentityProofStatus_eq

theorem noTwoSidedInv
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T) :
    C.noTwoSidedInvStatus =
      SM3db4aTNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualCoverage :=
  C.noTwoSidedInvStatus_eq

theorem nextPhase_is_SM3db4aU
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T) :
    C.nextPhaseStatus =
      SM3db4aTNextPhaseStatus.sm3db4aUExposeTerminalFoldResidualIdentityFields :=
  C.nextPhaseStatus_eq

end GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT

abbrev RegularGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularTerminalFoldResidualCoverageAuditSM3db4aT
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (I : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p wp) :
    RegularGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT b p wp :=
  GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT.fromInvariance I

def variableTerminalFoldResidualCoverageAuditSM3db4aT
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (I : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p wp) :
    VariableGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT β p wp :=
  GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT.fromInvariance I

structure SM3db4aTTerminalFoldResidualCoverageLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularCoverageAudit : RegularGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT b p regularWeight
  variableCoverageAudit : VariableGeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT β p variableWeight
  ledgerStatus : SM3db4aTLedgerStatus
  terminalFoldStateStatus : SM3db4aTTerminalFoldStateStatus
  terminalResidualCoverageStatus : SM3db4aTTerminalResidualCoverageStatus
  terminalCoverageExportStatus : SM3db4aTTerminalCoverageExportStatus
  nextPhaseStatus : SM3db4aTNextPhaseStatus
  regularExportStatus_eq :
    regularCoverageAudit.terminalCoverageExportStatus =
      SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  variableExportStatus_eq :
    variableCoverageAudit.terminalCoverageExportStatus =
      SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  regularNoTwoSidedInvStatus_eq :
    regularCoverageAudit.noTwoSidedInvStatus =
      SM3db4aTNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualCoverage
  variableNoTwoSidedInvStatus_eq :
    variableCoverageAudit.noTwoSidedInvStatus =
      SM3db4aTNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualCoverage
  ledgerStatus_eq :
    ledgerStatus = SM3db4aTLedgerStatus.terminalFoldResidualCoverageAuditClosed
  terminalFoldStateStatus_eq :
    terminalFoldStateStatus =
      SM3db4aTTerminalFoldStateStatus.terminalFoldStateFromAccumulatedEntryFold
  terminalResidualCoverageStatus_eq :
    terminalResidualCoverageStatus =
      SM3db4aTTerminalResidualCoverageStatus.terminalResidualCoverageFromAccumulatedResidualAndFoldOrder
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aTNextPhaseStatus.sm3db4aUExposeTerminalFoldResidualIdentityFields

namespace SM3db4aTTerminalFoldResidualCoverageLedger

def fromRegularAndVariableInvariance
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularInvariance : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p regularWeight)
    (variableInvariance : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p variableWeight) :
    SM3db4aTTerminalFoldResidualCoverageLedger b β p regularWeight variableWeight where
  regularCoverageAudit := regularTerminalFoldResidualCoverageAuditSM3db4aT regularInvariance
  variableCoverageAudit := variableTerminalFoldResidualCoverageAuditSM3db4aT variableInvariance
  ledgerStatus := SM3db4aTLedgerStatus.terminalFoldResidualCoverageAuditClosed
  terminalFoldStateStatus :=
    SM3db4aTTerminalFoldStateStatus.terminalFoldStateFromAccumulatedEntryFold
  terminalResidualCoverageStatus :=
    SM3db4aTTerminalResidualCoverageStatus.terminalResidualCoverageFromAccumulatedResidualAndFoldOrder
  terminalCoverageExportStatus :=
    SM3db4aTTerminalCoverageExportStatus.terminalCoverageSourceBlockedUntilTerminalIdentityFields
  nextPhaseStatus :=
    SM3db4aTNextPhaseStatus.sm3db4aUExposeTerminalFoldResidualIdentityFields
  regularExportStatus_eq := by
    rfl
  variableExportStatus_eq := by
    rfl
  regularNoTwoSidedInvStatus_eq := by
    rfl
  variableNoTwoSidedInvStatus_eq := by
    rfl
  ledgerStatus_eq := by
    rfl
  terminalFoldStateStatus_eq := by
    rfl
  terminalResidualCoverageStatus_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3db4aTTerminalFoldResidualCoverageLedger

end Smoke

end CNNA.PillarA.Arithmetic
