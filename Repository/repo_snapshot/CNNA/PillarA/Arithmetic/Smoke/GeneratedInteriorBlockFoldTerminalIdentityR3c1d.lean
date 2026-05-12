import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3c1dTerminalIdentityStatus where
  | terminalIdentityFromR3c1cInvarianceAndTerminalCoverage
  deriving DecidableEq, Repr

inductive SM3eRr3c1dTracePivotCoverageStatus where
  | sourceFromSM3db3RTracePivotCoverage
  deriving DecidableEq, Repr

inductive SM3eRr3c1dTerminalFoldResidualCoverageStatus where
  | sourceFromSM3db4aRTerminalFoldResidualCoverage
  deriving DecidableEq, Repr

inductive SM3eRr3c1dTerminalCoverageAuditStatus where
  | terminalCoverageNotYetExposedBySM3db3ROrSM3db4aR
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNoAccumulatedEntryCancellationStatus where
  | noAccumulatedEntryCancellationInvariantInTerminalIdentity
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNoProductIdentityProofStatus where
  | noProductIdentityProofInTerminalIdentity
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNoTwoSidedInvStatus where
  | noTwoSidedInvInTerminalIdentity
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInTerminalIdentity
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentity
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentity
  deriving DecidableEq, Repr

inductive SM3eRr3c1dNextPhaseStatus where
  | sm3eRr3c1eAccumulatedEntryCancellationAdapter
  | sm3db3aOrSM3db4aTerminalCoverageSharpening
  deriving DecidableEq, Repr

structure GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d
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
  auditStatus : SM3eRr3c1dTerminalCoverageAuditStatus
  tracePivotCoverageStatus : SM3eRr3c1dTracePivotCoverageStatus
  terminalFoldResidualCoverageStatus : SM3eRr3c1dTerminalFoldResidualCoverageStatus
  noAccumulatedEntryCancellationStatus : SM3eRr3c1dNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3eRr3c1dNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1dNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3eRr3c1dNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRr3c1dNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRr3c1dNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1dNextPhaseStatus
  invarianceStatus_eq :
    invariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  auditStatus_eq :
    auditStatus =
      SM3eRr3c1dTerminalCoverageAuditStatus.terminalCoverageNotYetExposedBySM3db3ROrSM3db4aR
  tracePivotCoverageStatus_eq :
    tracePivotCoverageStatus =
      SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalFoldResidualCoverageStatus_eq :
    terminalFoldResidualCoverageStatus =
      SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRr3c1dNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentity
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRr3c1dNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentity
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRr3c1dNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentity
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening

namespace GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d

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
    GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d Cell p A P wp W E K T where
  invariance := I
  auditStatus :=
    SM3eRr3c1dTerminalCoverageAuditStatus.terminalCoverageNotYetExposedBySM3db3ROrSM3db4aR
  tracePivotCoverageStatus :=
    SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalFoldResidualCoverageStatus :=
    SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage
  noAccumulatedEntryCancellationStatus :=
    SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity
  noProductIdentityProofStatus :=
    SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity
  noTwoSidedInvStatus := SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity
  noInteriorEliminationDataStatus :=
    SM3eRr3c1dNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentity
  noDtnDataStatus :=
    SM3eRr3c1dNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentity
  noArithmeticTargetStatus :=
    SM3eRr3c1dNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentity
  nextPhaseStatus := SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening
  invarianceStatus_eq :=
    I.invarianceStatus_eq
  trace_source_eq_SM3db3R :=
    I.trace_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    I.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    I.accumulatedFoldSource_eq_SM3db4aR
  auditStatus_eq := by
    rfl
  tracePivotCoverageStatus_eq := by
    rfl
  terminalFoldResidualCoverageStatus_eq := by
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

theorem nextPhase_is_terminalCoverageSharpening
    (A0 : GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d Cell p A P wp W E K T) :
    A0.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening :=
  A0.nextPhaseStatus_eq

end GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d

structure GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d
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
  tracePivotCoverageStatus : SM3eRr3c1dTracePivotCoverageStatus
  terminalFoldResidualCoverageStatus : SM3eRr3c1dTerminalFoldResidualCoverageStatus
  leftBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i i = 1
  leftBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorLeftBlockFold W T i j = 0
  rightBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i i = 1
  rightBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorRightBlockFold W T i j = 0
  invarianceStatus_eq :
    invariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  tracePivotCoverageStatus_eq :
    tracePivotCoverageStatus =
      SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalFoldResidualCoverageStatus_eq :
    terminalFoldResidualCoverageStatus =
      SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage

namespace GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d

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

def fromSM3db4aUTerminalIdentityFieldCertificate
    (C : GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d Cell p A P wp W E K T where
  invariance := C.invariance
  tracePivotCoverageStatus :=
    SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalFoldResidualCoverageStatus :=
    SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage
  leftBlockFold_eq_identity :=
    C.leftBlockFold_eq_identity
  rightBlockFold_eq_identity :=
    C.rightBlockFold_eq_identity
  leftBlockFold_diagonal :=
    C.leftBlockFold_diagonal
  leftBlockFold_offdiag :=
    C.leftBlockFold_offdiag
  rightBlockFold_diagonal :=
    C.rightBlockFold_diagonal
  rightBlockFold_offdiag :=
    C.rightBlockFold_offdiag
  invarianceStatus_eq :=
    C.invarianceStatus_eq
  trace_source_eq_SM3db3R :=
    C.trace_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    C.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    C.accumulatedFoldSource_eq_SM3db4aR
  tracePivotCoverageStatus_eq := by
    rfl
  terminalFoldResidualCoverageStatus_eq := by
    rfl

end GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d

structure GeneratedInteriorBlockFoldTerminalIdentityR3c1d
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
  terminalCoverage : GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d Cell p A P wp W E K T
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  terminalIdentityStatus : SM3eRr3c1dTerminalIdentityStatus
  tracePivotCoverageStatus : SM3eRr3c1dTracePivotCoverageStatus
  terminalFoldResidualCoverageStatus : SM3eRr3c1dTerminalFoldResidualCoverageStatus
  noAccumulatedEntryCancellationStatus : SM3eRr3c1dNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3eRr3c1dNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1dNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3eRr3c1dNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRr3c1dNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRr3c1dNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1dNextPhaseStatus
  invariance_eq_terminalCoverage : invariance = terminalCoverage.invariance
  leftBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftFoldSum_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldStepSourceR3c1c
        W T invariance.localStepCancellation.bridge.traceLocalStepInvariant i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightFoldSum_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldStepSourceR3c1c
        W T invariance.localStepCancellation.bridge.traceLocalStepInvariant i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftAccumulatedConvolution_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedLeftConvolution W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightAccumulatedConvolution_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedRightConvolution W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i i = 1
  leftBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorLeftBlockFold W T i j = 0
  rightBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i i = 1
  rightBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorRightBlockFold W T i j = 0
  leftAccumulatedConvolution_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedLeftConvolution W T i i = 1
  leftAccumulatedConvolution_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorAccumulatedLeftConvolution W T i j = 0
  rightAccumulatedConvolution_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedRightConvolution W T i i = 1
  rightAccumulatedConvolution_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorAccumulatedRightConvolution W T i j = 0
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    invariance.blockFoldNormalForm.accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  terminalIdentityStatus_eq :
    terminalIdentityStatus =
      SM3eRr3c1dTerminalIdentityStatus.terminalIdentityFromR3c1cInvarianceAndTerminalCoverage
  tracePivotCoverageStatus_eq :
    tracePivotCoverageStatus =
      SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalFoldResidualCoverageStatus_eq :
    terminalFoldResidualCoverageStatus =
      SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRr3c1dNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentity
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRr3c1dNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentity
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRr3c1dNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentity
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter

namespace GeneratedInteriorBlockFoldTerminalIdentityR3c1d

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

def fromTerminalCoverage
    (C : GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T where
  terminalCoverage := C
  invariance := C.invariance
  terminalIdentityStatus :=
    SM3eRr3c1dTerminalIdentityStatus.terminalIdentityFromR3c1cInvarianceAndTerminalCoverage
  tracePivotCoverageStatus :=
    SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalFoldResidualCoverageStatus :=
    SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage
  noAccumulatedEntryCancellationStatus :=
    SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity
  noProductIdentityProofStatus :=
    SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity
  noTwoSidedInvStatus := SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity
  noInteriorEliminationDataStatus :=
    SM3eRr3c1dNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalIdentity
  noDtnDataStatus :=
    SM3eRr3c1dNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalIdentity
  noArithmeticTargetStatus :=
    SM3eRr3c1dNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalIdentity
  nextPhaseStatus := SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  invariance_eq_terminalCoverage := by
    rfl
  leftBlockFold_eq_identity :=
    C.leftBlockFold_eq_identity
  rightBlockFold_eq_identity :=
    C.rightBlockFold_eq_identity
  leftFoldSum_eq_identity := by
    intro i j
    calc
      generatedInteriorLeftBlockFoldStepSourceR3c1c
          W T C.invariance.localStepCancellation.bridge.traceLocalStepInvariant i j =
          generatedInteriorLeftBlockFold W T i j :=
        C.invariance.leftFoldSumPreservation i j
      _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
        C.leftBlockFold_eq_identity i j
  rightFoldSum_eq_identity := by
    intro i j
    calc
      generatedInteriorRightBlockFoldStepSourceR3c1c
          W T C.invariance.localStepCancellation.bridge.traceLocalStepInvariant i j =
          generatedInteriorRightBlockFold W T i j :=
        C.invariance.rightFoldSumPreservation i j
      _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
        C.rightBlockFold_eq_identity i j
  leftAccumulatedConvolution_eq_identity := by
    intro i j
    calc
      generatedInteriorAccumulatedLeftConvolution W T i j =
          generatedInteriorLeftBlockFold W T i j :=
        C.invariance.blockFoldNormalForm.leftAccumulatedConvolution_eq_blockFold i j
      _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
        C.leftBlockFold_eq_identity i j
  rightAccumulatedConvolution_eq_identity := by
    intro i j
    calc
      generatedInteriorAccumulatedRightConvolution W T i j =
          generatedInteriorRightBlockFold W T i j :=
        C.invariance.blockFoldNormalForm.rightAccumulatedConvolution_eq_blockFold i j
      _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
        C.rightBlockFold_eq_identity i j
  leftBlockFold_diagonal :=
    C.leftBlockFold_diagonal
  leftBlockFold_offdiag :=
    C.leftBlockFold_offdiag
  rightBlockFold_diagonal :=
    C.rightBlockFold_diagonal
  rightBlockFold_offdiag :=
    C.rightBlockFold_offdiag
  leftAccumulatedConvolution_diagonal := by
    intro i
    calc
      generatedInteriorAccumulatedLeftConvolution W T i i =
          generatedInteriorLeftBlockFold W T i i :=
        C.invariance.blockFoldNormalForm.leftAccumulatedConvolution_eq_blockFold i i
      _ = 1 :=
        C.leftBlockFold_diagonal i
  leftAccumulatedConvolution_offdiag := by
    intro i j hij
    calc
      generatedInteriorAccumulatedLeftConvolution W T i j =
          generatedInteriorLeftBlockFold W T i j :=
        C.invariance.blockFoldNormalForm.leftAccumulatedConvolution_eq_blockFold i j
      _ = 0 :=
        C.leftBlockFold_offdiag i j hij
  rightAccumulatedConvolution_diagonal := by
    intro i
    calc
      generatedInteriorAccumulatedRightConvolution W T i i =
          generatedInteriorRightBlockFold W T i i :=
        C.invariance.blockFoldNormalForm.rightAccumulatedConvolution_eq_blockFold i i
      _ = 1 :=
        C.rightBlockFold_diagonal i
  rightAccumulatedConvolution_offdiag := by
    intro i j hij
    calc
      generatedInteriorAccumulatedRightConvolution W T i j =
          generatedInteriorRightBlockFold W T i j :=
        C.invariance.blockFoldNormalForm.rightAccumulatedConvolution_eq_blockFold i j
      _ = 0 :=
        C.rightBlockFold_offdiag i j hij
  trace_source_eq_SM3db3R :=
    C.trace_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    C.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    C.accumulatedFoldSource_eq_SM3db4aR
  terminalIdentityStatus_eq := by
    rfl
  tracePivotCoverageStatus_eq := by
    rfl
  terminalFoldResidualCoverageStatus_eq := by
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

theorem leftBlockFold_entry_eq_identity
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFold W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.leftBlockFold_eq_identity i j

theorem rightBlockFold_entry_eq_identity
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFold W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.rightBlockFold_eq_identity i j

theorem leftFoldSum_entry_eq_identity
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFoldStepSourceR3c1c
      W T D.invariance.localStepCancellation.bridge.traceLocalStepInvariant i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.leftFoldSum_eq_identity i j

theorem rightFoldSum_entry_eq_identity
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFoldStepSourceR3c1c
      W T D.invariance.localStepCancellation.bridge.traceLocalStepInvariant i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.rightFoldSum_eq_identity i j

theorem leftAccumulatedConvolution_entry_eq_identity
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedLeftConvolution W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.leftAccumulatedConvolution_eq_identity i j

theorem rightAccumulatedConvolution_entry_eq_identity
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedRightConvolution W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.rightAccumulatedConvolution_eq_identity i j

theorem noAccumulatedEntryCancellationInvariant
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T) :
    D.noAccumulatedEntryCancellationStatus =
      SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity :=
  D.noAccumulatedEntryCancellationStatus_eq

theorem nextPhase_is_r3c1e
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T) :
    D.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter :=
  D.nextPhaseStatus_eq

end GeneratedInteriorBlockFoldTerminalIdentityR3c1d

abbrev RegularGeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorBlockFoldTerminalIdentityR3c1d
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldTerminalIdentityR3c1d
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorBlockFoldTerminalIdentityR3c1d
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldTerminalIdentityR3c1d
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularBlockFoldTerminalCoverageAuditR3c1d
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (I : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p wp) :
    RegularGeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d b p wp :=
  GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d.fromInvariance I

def variableBlockFoldTerminalCoverageAuditR3c1d
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (I : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p wp) :
    VariableGeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d β p wp :=
  GeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d.fromInvariance I

def regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aU
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : RegularGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU b p wp) :
    RegularGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d b p wp :=
  GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d.fromSM3db4aUTerminalIdentityFieldCertificate C

def variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aU
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : VariableGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU β p wp) :
    VariableGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d β p wp :=
  GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d.fromSM3db4aUTerminalIdentityFieldCertificate C

def regularBlockFoldTerminalIdentityR3c1d
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : RegularGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d b p wp) :
    RegularGeneratedInteriorBlockFoldTerminalIdentityR3c1d b p wp :=
  GeneratedInteriorBlockFoldTerminalIdentityR3c1d.fromTerminalCoverage C

def variableBlockFoldTerminalIdentityR3c1d
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : VariableGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d β p wp) :
    VariableGeneratedInteriorBlockFoldTerminalIdentityR3c1d β p wp :=
  GeneratedInteriorBlockFoldTerminalIdentityR3c1d.fromTerminalCoverage C

structure SM3eRr3c1dTerminalCoverageAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAudit : RegularGeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d b p regularWeight
  variableAudit : VariableGeneratedInteriorBlockFoldTerminalCoverageAuditR3c1d β p variableWeight
  auditStatus : SM3eRr3c1dTerminalCoverageAuditStatus
  nextPhaseStatus : SM3eRr3c1dNextPhaseStatus
  regularNextPhaseStatus_eq :
    regularAudit.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening
  variableNextPhaseStatus_eq :
    variableAudit.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening
  auditStatus_eq :
    auditStatus =
      SM3eRr3c1dTerminalCoverageAuditStatus.terminalCoverageNotYetExposedBySM3db3ROrSM3db4aR
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening

namespace SM3eRr3c1dTerminalCoverageAuditLedger

def fromRegularAndVariableInvariance
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularInvariance : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p regularWeight)
    (variableInvariance : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p variableWeight) :
    SM3eRr3c1dTerminalCoverageAuditLedger b β p regularWeight variableWeight where
  regularAudit := regularBlockFoldTerminalCoverageAuditR3c1d regularInvariance
  variableAudit := variableBlockFoldTerminalCoverageAuditR3c1d variableInvariance
  auditStatus :=
    SM3eRr3c1dTerminalCoverageAuditStatus.terminalCoverageNotYetExposedBySM3db3ROrSM3db4aR
  nextPhaseStatus := SM3eRr3c1dNextPhaseStatus.sm3db3aOrSM3db4aTerminalCoverageSharpening
  regularNextPhaseStatus_eq := by
    rfl
  variableNextPhaseStatus_eq := by
    rfl
  auditStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3eRr3c1dTerminalCoverageAuditLedger

structure SM3eRr3c1dTerminalIdentityLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularTerminalIdentity : RegularGeneratedInteriorBlockFoldTerminalIdentityR3c1d b p regularWeight
  variableTerminalIdentity : VariableGeneratedInteriorBlockFoldTerminalIdentityR3c1d β p variableWeight
  terminalIdentityStatus : SM3eRr3c1dTerminalIdentityStatus
  nextPhaseStatus : SM3eRr3c1dNextPhaseStatus
  regularNextPhaseStatus_eq :
    regularTerminalIdentity.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  variableNextPhaseStatus_eq :
    variableTerminalIdentity.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  terminalIdentityStatus_eq :
    terminalIdentityStatus =
      SM3eRr3c1dTerminalIdentityStatus.terminalIdentityFromR3c1cInvarianceAndTerminalCoverage
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter

namespace SM3eRr3c1dTerminalIdentityLedger

def fromRegularAndVariableTerminalCoverage
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularCoverage : RegularGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d b p regularWeight)
    (variableCoverage : VariableGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d β p variableWeight) :
    SM3eRr3c1dTerminalIdentityLedger b β p regularWeight variableWeight where
  regularTerminalIdentity := regularBlockFoldTerminalIdentityR3c1d regularCoverage
  variableTerminalIdentity := variableBlockFoldTerminalIdentityR3c1d variableCoverage
  terminalIdentityStatus :=
    SM3eRr3c1dTerminalIdentityStatus.terminalIdentityFromR3c1cInvarianceAndTerminalCoverage
  nextPhaseStatus := SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  regularNextPhaseStatus_eq := by
    rfl
  variableNextPhaseStatus_eq := by
    rfl
  terminalIdentityStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3eRr3c1dTerminalIdentityLedger

end Smoke

end CNNA.PillarA.Arithmetic
