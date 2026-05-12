import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db4RTraceEntryFoldStatus where
  | traceEntryFoldFromSM3db3RTrace
  deriving DecidableEq, Repr

inductive SM3db4RTraceEvaluationStatus where
  | traceEvaluationFromTraceEntryFold
  deriving DecidableEq, Repr

inductive SM3db4RInverseCandidateEntryStatus where
  | generatedInteriorInverseCandidateEntryBuiltFromTrace
  deriving DecidableEq, Repr

inductive SM3db4RInverseCandidateSourceStatus where
  | inverseCandidateEntryFromSM3db3RTraceEvaluation
  deriving DecidableEq, Repr

inductive SM3db4RNotSM3daRCandidateStatus where
  | notSM3daRCandidateEntry
  deriving DecidableEq, Repr

inductive SM3db4RNotInteriorBlockDefinitionStatus where
  | notDefinedByGeneratedInteriorBlock
  deriving DecidableEq, Repr

inductive SM3db4RValidationStatus where
  | entryNotProductValidatedUntilSM3db7Rerun
  deriving DecidableEq, Repr

inductive SM3db4RNoMatrixInvStatus where
  | noMatrixInvForInverseCandidateEntry
  deriving DecidableEq, Repr

inductive SM3db4RNoFreeInverseEntryTableStatus where
  | noFreeInverseEntryTable
  deriving DecidableEq, Repr

inductive SM3db4RNoExternalInverseOracleStatus where
  | noExternalInverseOracleForInverseCandidateEntry
  deriving DecidableEq, Repr

inductive SM3db4RNoMatrixExportStatus where
  | noMatrixExportInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNoProductProofStatus where
  | noProductProofInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db4R
  deriving DecidableEq, Repr

inductive SM3db4RNextPositivePhase where
  | sm3db5RMatrixExportWithoutProductProof
  deriving DecidableEq, Repr

inductive SM3db4RGeneratedInteriorInverseCandidateEntryLedgerStatus where
  | generatedInteriorInverseCandidateEntryClosed
  deriving DecidableEq, Repr

structure GeneratedInteriorTraceEntryFold
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
  entry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  foldStatus : SM3db4RTraceEntryFoldStatus
  sourceStatus : SM3db3RTraceSourceStatus
  noMatrixInvStatus : SM3db4RNoMatrixInvStatus
  noFreeInverseEntryTableStatus : SM3db4RNoFreeInverseEntryTableStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noMatrixExportStatus : SM3db4RNoMatrixExportStatus
  noProductProofStatus : SM3db4RNoProductProofStatus
  noTwoSidedInvStatus : SM3db4RNoTwoSidedInvStatus
  trace_eq : trace = T
  entry_eq_traceStepUpdateRowResidual :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = (T.traceStepOf i).stepUpdate.rowResidual j
  source_eq_eliminationTrace : sourceStatus = T.sourceStatus
  source_eq_SM3cR_SM3dR :
    sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  foldStatus_eq :
    foldStatus = SM3db4RTraceEntryFoldStatus.traceEntryFoldFromSM3db3RTrace
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

namespace GeneratedInteriorTraceEntryFold

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


def fromTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorTraceEntryFold Cell p A P wp W E K T where
  trace := T
  entry := fun i j => (T.traceStepOf i).stepUpdate.rowResidual j
  foldStatus := SM3db4RTraceEntryFoldStatus.traceEntryFoldFromSM3db3RTrace
  sourceStatus := T.sourceStatus
  noMatrixInvStatus := SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus :=
    SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus := SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus := SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus := SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R
  trace_eq := by
    rfl
  entry_eq_traceStepUpdateRowResidual := by
    intro i j
    rfl
  source_eq_eliminationTrace := by
    rfl
  source_eq_SM3cR_SM3dR :=
    T.sourceStatus_eq
  foldStatus_eq := by
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

theorem source_eq_eliminationTrace_thm
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (F : GeneratedInteriorTraceEntryFold Cell p A P wp W E K T) :
    F.sourceStatus = T.sourceStatus :=
  F.source_eq_eliminationTrace

theorem source_eq_SM3cR_SM3dR_thm
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (F : GeneratedInteriorTraceEntryFold Cell p A P wp W E K T) :
    F.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps :=
  F.source_eq_SM3cR_SM3dR

theorem noMatrixExport
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (F : GeneratedInteriorTraceEntryFold Cell p A P wp W E K T) :
    F.noMatrixExportStatus = SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R :=
  F.noMatrixExportStatus_eq

end GeneratedInteriorTraceEntryFold

structure GeneratedInteriorTraceEvaluation
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
  entryFold : GeneratedInteriorTraceEntryFold Cell p A P wp W E K T
  entry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  evaluationStatus : SM3db4RTraceEvaluationStatus
  sourceStatus : SM3db4RInverseCandidateSourceStatus
  noMatrixInvStatus : SM3db4RNoMatrixInvStatus
  noFreeInverseEntryTableStatus : SM3db4RNoFreeInverseEntryTableStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noMatrixExportStatus : SM3db4RNoMatrixExportStatus
  noProductProofStatus : SM3db4RNoProductProofStatus
  noTwoSidedInvStatus : SM3db4RNoTwoSidedInvStatus
  trace_eq : trace = T
  entryFold_eq_fromTrace : entryFold = GeneratedInteriorTraceEntryFold.fromTrace T
  entry_eq_entryFold :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = entryFold.entry i j
  entry_eq_traceStepUpdateRowResidual :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = (T.traceStepOf i).stepUpdate.rowResidual j
  evaluationStatus_eq :
    evaluationStatus = SM3db4RTraceEvaluationStatus.traceEvaluationFromTraceEntryFold
  sourceStatus_eq :
    sourceStatus =
      SM3db4RInverseCandidateSourceStatus.inverseCandidateEntryFromSM3db3RTraceEvaluation
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

namespace GeneratedInteriorTraceEvaluation

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


def fromTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorTraceEvaluation Cell p A P wp W E K T where
  trace := T
  entryFold := GeneratedInteriorTraceEntryFold.fromTrace T
  entry := fun i j => (GeneratedInteriorTraceEntryFold.fromTrace T).entry i j
  evaluationStatus := SM3db4RTraceEvaluationStatus.traceEvaluationFromTraceEntryFold
  sourceStatus :=
    SM3db4RInverseCandidateSourceStatus.inverseCandidateEntryFromSM3db3RTraceEvaluation
  noMatrixInvStatus := SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noFreeInverseEntryTableStatus :=
    SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noMatrixExportStatus := SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  noProductProofStatus := SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  noTwoSidedInvStatus := SM3db4RNoTwoSidedInvStatus.noTwoSidedInvInSM3db4R
  trace_eq := by
    rfl
  entryFold_eq_fromTrace := by
    rfl
  entry_eq_entryFold := by
    intro i j
    rfl
  entry_eq_traceStepUpdateRowResidual := by
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

theorem entry_eq_traceStepUpdateRowResidual_thm
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (Q : GeneratedInteriorTraceEvaluation Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    Q.entry i j = (T.traceStepOf i).stepUpdate.rowResidual j :=
  Q.entry_eq_traceStepUpdateRowResidual i j

end GeneratedInteriorTraceEvaluation

structure GeneratedInteriorInverseCandidateEntry
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
  traceEvaluation : GeneratedInteriorTraceEvaluation Cell p A P wp W E K T
  entry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  candidateStatus : SM3db4RInverseCandidateEntryStatus
  sourceStatus : SM3db4RInverseCandidateSourceStatus
  notSM3daRCandidateStatus : SM3db4RNotSM3daRCandidateStatus
  notInteriorBlockDefinitionStatus : SM3db4RNotInteriorBlockDefinitionStatus
  validationStatus : SM3db4RValidationStatus
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
  nextPositivePhase : SM3db4RNextPositivePhase
  trace_eq : trace = T
  traceEvaluation_eq_fromTrace : traceEvaluation = GeneratedInteriorTraceEvaluation.fromTrace T
  entry_eq_traceEvaluation :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = traceEvaluation.entry i j
  entry_eq_traceStepUpdateRowResidual :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j = (T.traceStepOf i).stepUpdate.rowResidual j
  source_eq_eliminationTrace :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  candidateStatus_eq :
    candidateStatus =
      SM3db4RInverseCandidateEntryStatus.generatedInteriorInverseCandidateEntryBuiltFromTrace
  sourceStatus_eq :
    sourceStatus =
      SM3db4RInverseCandidateSourceStatus.inverseCandidateEntryFromSM3db3RTraceEvaluation
  notSM3daRCandidateStatus_eq :
    notSM3daRCandidateStatus =
      SM3db4RNotSM3daRCandidateStatus.notSM3daRCandidateEntry
  notInteriorBlockDefinitionStatus_eq :
    notInteriorBlockDefinitionStatus =
      SM3db4RNotInteriorBlockDefinitionStatus.notDefinedByGeneratedInteriorBlock
  validationStatus_eq :
    validationStatus =
      SM3db4RValidationStatus.entryNotProductValidatedUntilSM3db7Rerun
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
    nextPositivePhase = SM3db4RNextPositivePhase.sm3db5RMatrixExportWithoutProductProof

namespace GeneratedInteriorInverseCandidateEntry

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


def fromTraceEvaluation
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T where
  trace := T
  traceEvaluation := GeneratedInteriorTraceEvaluation.fromTrace T
  entry := fun i j => (GeneratedInteriorTraceEvaluation.fromTrace T).entry i j
  candidateStatus :=
    SM3db4RInverseCandidateEntryStatus.generatedInteriorInverseCandidateEntryBuiltFromTrace
  sourceStatus :=
    SM3db4RInverseCandidateSourceStatus.inverseCandidateEntryFromSM3db3RTraceEvaluation
  notSM3daRCandidateStatus :=
    SM3db4RNotSM3daRCandidateStatus.notSM3daRCandidateEntry
  notInteriorBlockDefinitionStatus :=
    SM3db4RNotInteriorBlockDefinitionStatus.notDefinedByGeneratedInteriorBlock
  validationStatus := SM3db4RValidationStatus.entryNotProductValidatedUntilSM3db7Rerun
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
  nextPositivePhase := SM3db4RNextPositivePhase.sm3db5RMatrixExportWithoutProductProof
  trace_eq := by
    rfl
  traceEvaluation_eq_fromTrace := by
    rfl
  entry_eq_traceEvaluation := by
    intro i j
    rfl
  entry_eq_traceStepUpdateRowResidual := by
    intro i j
    rfl
  source_eq_eliminationTrace :=
    T.sourceStatus_eq
  candidateStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  notSM3daRCandidateStatus_eq := by
    rfl
  notInteriorBlockDefinitionStatus_eq := by
    rfl
  validationStatus_eq := by
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

theorem source_eq_eliminationTrace_thm
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps :=
  I.source_eq_eliminationTrace

theorem noMatrixInv
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noMatrixInvStatus =
      SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry :=
  I.noMatrixInvStatus_eq

theorem noFreeInverseEntryTable
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable :=
  I.noFreeInverseEntryTableStatus_eq

theorem noExternalInverseOracle
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry :=
  I.noExternalInverseOracleStatus_eq

theorem noMatrixExport
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noMatrixExportStatus = SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R :=
  I.noMatrixExportStatus_eq

theorem noProductProof
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noProductProofStatus = SM3db4RNoProductProofStatus.noProductProofInSM3db4R :=
  I.noProductProofStatus_eq

end GeneratedInteriorInverseCandidateEntry

def traceEntryFold_from_eliminationTrace
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
    GeneratedInteriorTraceEntryFold Cell p A P wp W E K T :=
  GeneratedInteriorTraceEntryFold.fromTrace T

def traceEvaluation_from_traceEntryFold
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
    GeneratedInteriorTraceEvaluation Cell p A P wp W E K T :=
  GeneratedInteriorTraceEvaluation.fromTrace T

def inverseCandidateEntry_from_finiteEliminationTrace
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
    GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T :=
  GeneratedInteriorInverseCandidateEntry.fromTraceEvaluation T

def inverseCandidateEntry_from_treeRecursiveElimination
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
    GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T :=
  inverseCandidateEntry_from_finiteEliminationTrace T

theorem inverseCandidateEntry_source_eq_eliminationTrace
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
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.trace = T :=
  I.trace_eq

theorem inverseCandidateEntry_source_eq_SM3cR_SM3dR
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
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps :=
  I.source_eq_eliminationTrace

theorem noMatrixInv_for_inverseCandidateEntry
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
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noMatrixInvStatus =
      SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry :=
  I.noMatrixInvStatus_eq

theorem noFreeInverseEntryTable
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
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable :=
  I.noFreeInverseEntryTableStatus_eq

theorem noExternalInverseOracle_for_inverseCandidateEntry
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
    (I : GeneratedInteriorInverseCandidateEntry Cell p A P wp W E K T) :
    I.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry :=
  I.noExternalInverseOracleStatus_eq

def regularGeneratedInteriorInverseCandidateEntry
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorInverseCandidateEntry
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp) :=
  inverseCandidateEntry_from_finiteEliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableGeneratedInteriorInverseCandidateEntry
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorInverseCandidateEntry
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp) :=
  inverseCandidateEntry_from_finiteEliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3db4RGeneratedInteriorInverseCandidateEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3db4RGeneratedInteriorInverseCandidateEntryLedgerStatus
  sm3db3Ledger :
    SM3db3RGeneratedInteriorEliminationTraceLedger b β p regularWeight variableWeight
      regularPivot variablePivot
  regularTrace :
    GeneratedInteriorEliminationTrace
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
  variableTrace :
    GeneratedInteriorEliminationTrace
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
  regularInverseCandidateEntry :
    GeneratedInteriorInverseCandidateEntry
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
  variableInverseCandidateEntry :
    GeneratedInteriorInverseCandidateEntry
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
  sm3db3Ledger_eq_main :
    sm3db3Ledger = sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularTrace_eq_main :
    regularTrace = regularGeneratedInteriorEliminationTrace b p regularWeight
  variableTrace_eq_main :
    variableTrace = variableGeneratedInteriorEliminationTrace β p variableWeight
  regularCandidate_eq_main :
    regularInverseCandidateEntry = regularGeneratedInteriorInverseCandidateEntry b p regularWeight
  variableCandidate_eq_main :
    variableInverseCandidateEntry = variableGeneratedInteriorInverseCandidateEntry β p variableWeight
  regularSource_eq_SM3cR_SM3dR :
    regularTrace.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  variableSource_eq_SM3cR_SM3dR :
    variableTrace.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  regularNoMatrixInv :
    regularInverseCandidateEntry.noMatrixInvStatus =
      SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  variableNoMatrixInv :
    variableInverseCandidateEntry.noMatrixInvStatus =
      SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  regularNoFreeInverseEntryTable :
    regularInverseCandidateEntry.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  variableNoFreeInverseEntryTable :
    variableInverseCandidateEntry.noFreeInverseEntryTableStatus =
      SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  regularNoExternalInverseOracle :
    regularInverseCandidateEntry.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  variableNoExternalInverseOracle :
    variableInverseCandidateEntry.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  regularNoMatrixExport :
    regularInverseCandidateEntry.noMatrixExportStatus =
      SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  variableNoMatrixExport :
    variableInverseCandidateEntry.noMatrixExportStatus =
      SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R
  regularNoProductProof :
    regularInverseCandidateEntry.noProductProofStatus =
      SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  variableNoProductProof :
    variableInverseCandidateEntry.noProductProofStatus =
      SM3db4RNoProductProofStatus.noProductProofInSM3db4R
  regularNextPositivePhase :
    regularInverseCandidateEntry.nextPositivePhase =
      SM3db4RNextPositivePhase.sm3db5RMatrixExportWithoutProductProof
  variableNextPositivePhase :
    variableInverseCandidateEntry.nextPositivePhase =
      SM3db4RNextPositivePhase.sm3db5RMatrixExportWithoutProductProof
  status_eq_closed :
    status =
      SM3db4RGeneratedInteriorInverseCandidateEntryLedgerStatus.generatedInteriorInverseCandidateEntryClosed

def sm3db4RGeneratedInteriorInverseCandidateEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status :=
    SM3db4RGeneratedInteriorInverseCandidateEntryLedgerStatus.generatedInteriorInverseCandidateEntryClosed
  sm3db3Ledger :=
    sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularTrace := regularGeneratedInteriorEliminationTrace b p regularWeight
  variableTrace := variableGeneratedInteriorEliminationTrace β p variableWeight
  regularInverseCandidateEntry :=
    regularGeneratedInteriorInverseCandidateEntry b p regularWeight
  variableInverseCandidateEntry :=
    variableGeneratedInteriorInverseCandidateEntry β p variableWeight
  sm3db3Ledger_eq_main := by
    rfl
  regularTrace_eq_main := by
    rfl
  variableTrace_eq_main := by
    rfl
  regularCandidate_eq_main := by
    rfl
  variableCandidate_eq_main := by
    rfl
  regularSource_eq_SM3cR_SM3dR := by
    rfl
  variableSource_eq_SM3cR_SM3dR := by
    rfl
  regularNoMatrixInv := by
    rfl
  variableNoMatrixInv := by
    rfl
  regularNoFreeInverseEntryTable := by
    rfl
  variableNoFreeInverseEntryTable := by
    rfl
  regularNoExternalInverseOracle := by
    rfl
  variableNoExternalInverseOracle := by
    rfl
  regularNoMatrixExport := by
    rfl
  variableNoMatrixExport := by
    rfl
  regularNoProductProof := by
    rfl
  variableNoProductProof := by
    rfl
  regularNextPositivePhase := by
    rfl
  variableNextPositivePhase := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3db4RGeneratedInteriorInverseCandidateEntryLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3db4RGeneratedInteriorInverseCandidateEntryLedgerStatus.generatedInteriorInverseCandidateEntryClosed := by
  rfl

theorem sm3db4RGeneratedInteriorInverseCandidateEntryLedger_regularNoMatrixExport
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularInverseCandidateEntry.noMatrixExportStatus =
      SM3db4RNoMatrixExportStatus.noMatrixExportInSM3db4R := by
  rfl

theorem sm3db4RGeneratedInteriorInverseCandidateEntryLedger_variableNoExternalInverseOracle
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot).variableInverseCandidateEntry.noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry := by
  rfl

theorem sm3db4RGeneratedInteriorInverseCandidateEntryLedger_regularNextPositivePhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db4RGeneratedInteriorInverseCandidateEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularInverseCandidateEntry.nextPositivePhase =
      SM3db4RNextPositivePhase.sm3db5RMatrixExportWithoutProductProof := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
