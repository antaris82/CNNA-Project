import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db3RTraceStepStatus where
  | traceStepFromSM3db2RLocalEliminationStep
  deriving DecidableEq, Repr

inductive SM3db3RTraceStatus where
  | generatedInteriorEliminationTraceClosed
  deriving DecidableEq, Repr

inductive SM3db3RTerminationStatus where
  | terminatesByFiniteInteriorCarrier
  deriving DecidableEq, Repr

inductive SM3db3RTraceSourceStatus where
  | traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  deriving DecidableEq, Repr

inductive SM3db3RNoExternalTraceOracleStatus where
  | noExternalTraceOracle
  deriving DecidableEq, Repr

inductive SM3db3RNoExternalOrderOracleStatus where
  | noExternalOrderOracle
  deriving DecidableEq, Repr

inductive SM3db3RNoFreePivotListStatus where
  | noFreePivotList
  deriving DecidableEq, Repr

inductive SM3db3RNoInverseEntryFunctionStatus where
  | noInverseEntryFunctionInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNoMatrixExportStatus where
  | noMatrixExportInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNoProductProofStatus where
  | noProductProofInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNoMatrixInvStatus where
  | noMatrixInvInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db3R
  deriving DecidableEq, Repr

inductive SM3db3RNextPositivePhase where
  | sm3db4RGeneratedInteriorInverseCandidateEntry
  deriving DecidableEq, Repr

inductive SM3db3RGeneratedInteriorEliminationTraceLedgerStatus where
  | generatedInteriorEliminationTraceClosed
  deriving DecidableEq, Repr

structure GeneratedInteriorEliminationTraceStep
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) where
  localStep : GeneratedInteriorEliminationStep Cell p A P wp W E K
  pivotDatum : GeneratedInteriorPivotDatum Cell p A P wp W E K
  pivotIndex : GeneratedInteriorIndex A
  pivotNode : GeneratedInteriorEliminationNode Cell p A P wp W K.candidate
  residualDatum : GeneratedInteriorResidualDatum Cell p A P wp W E K S.pivotDatum
  stepUpdate : GeneratedInteriorStepUpdate Cell p A P wp W E K S.pivotDatum S.residualDatum
  traceStepStatus : SM3db3RTraceStepStatus
  noExternalTraceOracleStatus : SM3db3RNoExternalTraceOracleStatus
  noExternalOrderOracleStatus : SM3db3RNoExternalOrderOracleStatus
  noFreePivotListStatus : SM3db3RNoFreePivotListStatus
  noInverseEntryFunctionStatus : SM3db3RNoInverseEntryFunctionStatus
  noMatrixExportStatus : SM3db3RNoMatrixExportStatus
  noTwoSidedInvStatus : SM3db3RNoTwoSidedInvStatus
  noProductProofStatus : SM3db3RNoProductProofStatus
  localStep_eq_SM3db2R_step : localStep = S
  pivotDatum_eq_localStepPivot : pivotDatum = S.pivotDatum
  pivotIndex_eq_localStepPivotIndex : pivotIndex = S.pivotDatum.pivotIndex
  pivotNode_eq_localStepPivotNode : pivotNode = S.pivotDatum.node
  residualDatum_eq_localStepResidual : residualDatum = S.residualDatum
  stepUpdate_eq_localStepUpdate : stepUpdate = S.stepUpdate
  localStep_from_SM3db2R :
    localStep.stepStatus =
      SM3db2REliminationStepStatus.generatedInteriorEliminationLocalStepClosed
  pivot_bound_to_SM3db1R_node :
    S.pivotDatum.node = K.nodeOf S.pivotDatum.pivotIndex
  residual_eq_SM3cR_interiorBlock :
    ∀ j : GeneratedInteriorIndex A,
      S.residualDatum.rowResidual j =
        generatedInteriorLocalRowResidual W S.pivotDatum.pivotIndex j
  columnResidual_eq_SM3cR_interiorBlock :
    ∀ i : GeneratedInteriorIndex A,
      S.residualDatum.columnResidual i =
        generatedInteriorLocalColumnResidual W S.pivotDatum.pivotIndex i
  traceStepStatus_eq :
    traceStepStatus =
      SM3db3RTraceStepStatus.traceStepFromSM3db2RLocalEliminationStep
  noExternalTraceOracleStatus_eq :
    noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  noExternalOrderOracleStatus_eq :
    noExternalOrderOracleStatus =
      SM3db3RNoExternalOrderOracleStatus.noExternalOrderOracle
  noFreePivotListStatus_eq :
    noFreePivotListStatus = SM3db3RNoFreePivotListStatus.noFreePivotList
  noInverseEntryFunctionStatus_eq :
    noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R
  noProductProofStatus_eq :
    noProductProofStatus = SM3db3RNoProductProofStatus.noProductProofInSM3db3R

namespace GeneratedInteriorEliminationTraceStep

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
variable {S : GeneratedInteriorEliminationStep Cell p A P wp W E K}

def fromLocalEliminationStep
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    GeneratedInteriorEliminationTraceStep Cell p A P wp W E K S where
  localStep := S
  pivotDatum := S.pivotDatum
  pivotIndex := S.pivotDatum.pivotIndex
  pivotNode := S.pivotDatum.node
  residualDatum := S.residualDatum
  stepUpdate := S.stepUpdate
  traceStepStatus :=
    SM3db3RTraceStepStatus.traceStepFromSM3db2RLocalEliminationStep
  noExternalTraceOracleStatus :=
    SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  noExternalOrderOracleStatus :=
    SM3db3RNoExternalOrderOracleStatus.noExternalOrderOracle
  noFreePivotListStatus := SM3db3RNoFreePivotListStatus.noFreePivotList
  noInverseEntryFunctionStatus :=
    SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R
  noMatrixExportStatus := SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R
  noTwoSidedInvStatus := SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R
  noProductProofStatus := SM3db3RNoProductProofStatus.noProductProofInSM3db3R
  localStep_eq_SM3db2R_step := by
    rfl
  pivotDatum_eq_localStepPivot := by
    rfl
  pivotIndex_eq_localStepPivotIndex := by
    rfl
  pivotNode_eq_localStepPivotNode := by
    rfl
  residualDatum_eq_localStepResidual := by
    rfl
  stepUpdate_eq_localStepUpdate := by
    rfl
  localStep_from_SM3db2R :=
    S.stepStatus_eq
  pivot_bound_to_SM3db1R_node :=
    S.pivot_from_carrierNode
  residual_eq_SM3cR_interiorBlock := by
    intro j
    exact S.residualDatum.rowResidual_eq_interiorBlock j
  columnResidual_eq_SM3cR_interiorBlock := by
    intro i
    exact S.residualDatum.columnResidual_eq_interiorBlock i
  traceStepStatus_eq := by
    rfl
  noExternalTraceOracleStatus_eq := by
    rfl
  noExternalOrderOracleStatus_eq := by
    rfl
  noFreePivotListStatus_eq := by
    rfl
  noInverseEntryFunctionStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noProductProofStatus_eq := by
    rfl

theorem traceStep_from_localEliminationStep
    (T : GeneratedInteriorEliminationTraceStep Cell p A P wp W E K S) :
    T.localStep = S :=
  T.localStep_eq_SM3db2R_step

theorem traceStep_localStep_eq_SM3db2R_step
    (T : GeneratedInteriorEliminationTraceStep Cell p A P wp W E K S) :
    T.localStep.stepStatus =
      SM3db2REliminationStepStatus.generatedInteriorEliminationLocalStepClosed :=
  T.localStep_from_SM3db2R

theorem traceStep_pivot_bound_to_SM3db1R_node
    (T : GeneratedInteriorEliminationTraceStep Cell p A P wp W E K S) :
    S.pivotDatum.node = K.nodeOf S.pivotDatum.pivotIndex :=
  T.pivot_bound_to_SM3db1R_node

theorem traceStep_residual_eq_SM3cR_interiorBlock
    (T : GeneratedInteriorEliminationTraceStep Cell p A P wp W E K S)
    (j : GeneratedInteriorIndex A) :
    S.residualDatum.rowResidual j =
      generatedInteriorLocalRowResidual W S.pivotDatum.pivotIndex j :=
  T.residual_eq_SM3cR_interiorBlock j

end GeneratedInteriorEliminationTraceStep

structure GeneratedInteriorEliminationTrace
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) where
  carrier : GeneratedInteriorEliminationCarrier Cell p A P wp W E
  traceIndexCarrier : Finset (GeneratedInteriorIndex A)
  localStepOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationStep Cell p A P wp W E K
  traceStepOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationTraceStep Cell p A P wp W E K (localStepOf i)
  traceLength : Nat
  traceStatus : SM3db3RTraceStatus
  terminationStatus : SM3db3RTerminationStatus
  sourceStatus : SM3db3RTraceSourceStatus
  noExternalTraceOracleStatus : SM3db3RNoExternalTraceOracleStatus
  noExternalOrderOracleStatus : SM3db3RNoExternalOrderOracleStatus
  noFreePivotListStatus : SM3db3RNoFreePivotListStatus
  noInverseEntryFunctionStatus : SM3db3RNoInverseEntryFunctionStatus
  noMatrixExportStatus : SM3db3RNoMatrixExportStatus
  noTwoSidedInvStatus : SM3db3RNoTwoSidedInvStatus
  noProductProofStatus : SM3db3RNoProductProofStatus
  noMatrixInvStatus : SM3db3RNoMatrixInvStatus
  noDtnDataStatus : SM3db3RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db3RNoArithmeticTargetStatus
  nextPositivePhase : SM3db3RNextPositivePhase
  carrier_eq : carrier = K
  traceIndexCarrier_eq_carrierIndexCarrier : traceIndexCarrier = K.indexCarrier
  traceLength_eq_traceIndexCarrier_card : traceLength = traceIndexCarrier.card
  localStepOf_eq_SM3db2R_step :
    ∀ i : GeneratedInteriorIndex A,
      localStepOf i = localStep_from_SM3db1R_node K i
  traceStep_localStep_eq_SM3db2R_step :
    ∀ i : GeneratedInteriorIndex A,
      (traceStepOf i).localStep = localStepOf i
  traceStep_pivot_bound_to_SM3db1R_node :
    ∀ i : GeneratedInteriorIndex A,
      (localStepOf i).pivotDatum.node =
        K.nodeOf (localStepOf i).pivotDatum.pivotIndex
  traceStep_residual_eq_SM3cR_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      (localStepOf i).residualDatum.rowResidual j =
        generatedInteriorLocalRowResidual W (localStepOf i).pivotDatum.pivotIndex j
  traceStep_columnResidual_eq_SM3cR_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      (localStepOf i).residualDatum.columnResidual j =
        generatedInteriorLocalColumnResidual W (localStepOf i).pivotDatum.pivotIndex j
  traceStatus_eq :
    traceStatus = SM3db3RTraceStatus.generatedInteriorEliminationTraceClosed
  terminationStatus_eq :
    terminationStatus = SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier
  sourceStatus_eq :
    sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  noExternalTraceOracleStatus_eq :
    noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  noExternalOrderOracleStatus_eq :
    noExternalOrderOracleStatus =
      SM3db3RNoExternalOrderOracleStatus.noExternalOrderOracle
  noFreePivotListStatus_eq :
    noFreePivotListStatus = SM3db3RNoFreePivotListStatus.noFreePivotList
  noInverseEntryFunctionStatus_eq :
    noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R
  noProductProofStatus_eq :
    noProductProofStatus = SM3db3RNoProductProofStatus.noProductProofInSM3db3R
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db3RNoMatrixInvStatus.noMatrixInvInSM3db3R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db3RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db3R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db3RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db3R
  nextPositivePhase_eq :
    nextPositivePhase =
      SM3db3RNextPositivePhase.sm3db4RGeneratedInteriorInverseCandidateEntry

namespace GeneratedInteriorEliminationTrace

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

def fromFiniteCarrier
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    GeneratedInteriorEliminationTrace Cell p A P wp W E K where
  carrier := K
  traceIndexCarrier := K.indexCarrier
  localStepOf := fun i => localStep_from_SM3db1R_node K i
  traceStepOf := fun i =>
    GeneratedInteriorEliminationTraceStep.fromLocalEliminationStep
      (localStep_from_SM3db1R_node K i)
  traceLength := K.indexCarrier.card
  traceStatus := SM3db3RTraceStatus.generatedInteriorEliminationTraceClosed
  terminationStatus := SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier
  sourceStatus :=
    SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  noExternalTraceOracleStatus :=
    SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  noExternalOrderOracleStatus :=
    SM3db3RNoExternalOrderOracleStatus.noExternalOrderOracle
  noFreePivotListStatus := SM3db3RNoFreePivotListStatus.noFreePivotList
  noInverseEntryFunctionStatus :=
    SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R
  noMatrixExportStatus := SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R
  noTwoSidedInvStatus := SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R
  noProductProofStatus := SM3db3RNoProductProofStatus.noProductProofInSM3db3R
  noMatrixInvStatus := SM3db3RNoMatrixInvStatus.noMatrixInvInSM3db3R
  noDtnDataStatus :=
    SM3db3RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db3R
  noArithmeticTargetStatus :=
    SM3db3RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db3R
  nextPositivePhase :=
    SM3db3RNextPositivePhase.sm3db4RGeneratedInteriorInverseCandidateEntry
  carrier_eq := by
    rfl
  traceIndexCarrier_eq_carrierIndexCarrier := by
    rfl
  traceLength_eq_traceIndexCarrier_card := by
    rfl
  localStepOf_eq_SM3db2R_step := by
    intro i
    rfl
  traceStep_localStep_eq_SM3db2R_step := by
    intro i
    rfl
  traceStep_pivot_bound_to_SM3db1R_node := by
    intro i
    exact (localStep_from_SM3db1R_node K i).pivot_from_carrierNode
  traceStep_residual_eq_SM3cR_interiorBlock := by
    intro i j
    exact (localStep_from_SM3db1R_node K i).residualDatum.rowResidual_eq_interiorBlock j
  traceStep_columnResidual_eq_SM3cR_interiorBlock := by
    intro i j
    exact (localStep_from_SM3db1R_node K i).residualDatum.columnResidual_eq_interiorBlock j
  traceStatus_eq := by
    rfl
  terminationStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  noExternalTraceOracleStatus_eq := by
    rfl
  noExternalOrderOracleStatus_eq := by
    rfl
  noFreePivotListStatus_eq := by
    rfl
  noInverseEntryFunctionStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noProductProofStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPositivePhase_eq := by
    rfl


def fromTreeRecursiveProfile
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    GeneratedInteriorEliminationTrace Cell p A P wp W E K :=
  fromFiniteCarrier K

theorem terminates
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    T.terminationStatus = SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier :=
  T.terminationStatus_eq

theorem source_eq_SM3cR_SM3dR
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps :=
  T.sourceStatus_eq

theorem noExternalTraceOracle
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    T.noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle :=
  T.noExternalTraceOracleStatus_eq

theorem noInverseEntryFunction
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    T.noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R :=
  T.noInverseEntryFunctionStatus_eq

theorem noMatrixExport
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    T.noMatrixExportStatus = SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R :=
  T.noMatrixExportStatus_eq

theorem noTwoSidedInv
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    T.noTwoSidedInvStatus = SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R :=
  T.noTwoSidedInvStatus_eq

end GeneratedInteriorEliminationTrace

def traceStep_from_localEliminationStep
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    GeneratedInteriorEliminationTraceStep Cell p A P wp W E K S :=
  GeneratedInteriorEliminationTraceStep.fromLocalEliminationStep S

def GeneratedInteriorEliminationTrace_from_finiteCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    GeneratedInteriorEliminationTrace Cell p A P wp W E K :=
  GeneratedInteriorEliminationTrace.fromFiniteCarrier K

def GeneratedInteriorEliminationTrace_from_treeRecursiveProfile
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    GeneratedInteriorEliminationTrace Cell p A P wp W E K :=
  GeneratedInteriorEliminationTrace.fromTreeRecursiveProfile K

theorem generatedInteriorEliminationTrace_terminates
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
    T.terminationStatus = SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier :=
  T.terminationStatus_eq

theorem generatedInteriorEliminationTrace_source_eq_SM3cR_SM3dR
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
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps :=
  T.sourceStatus_eq

theorem noExternalTraceOracle
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
    T.noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle :=
  T.noExternalTraceOracleStatus_eq

theorem trace_noInverseEntryFunction
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
    T.noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R :=
  T.noInverseEntryFunctionStatus_eq

theorem trace_noMatrixExport
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
    T.noMatrixExportStatus = SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R :=
  T.noMatrixExportStatus_eq

theorem trace_noTwoSidedInv
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
    T.noTwoSidedInvStatus = SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R :=
  T.noTwoSidedInvStatus_eq

def regularGeneratedInteriorEliminationTrace
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationTrace
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp) :=
  GeneratedInteriorEliminationTrace_from_finiteCarrier
    (regularGeneratedInteriorEliminationCarrier b p wp)

def variableGeneratedInteriorEliminationTrace
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationTrace
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp) :=
  GeneratedInteriorEliminationTrace_from_finiteCarrier
    (variableGeneratedInteriorEliminationCarrier β p wp)

structure SM3db3RGeneratedInteriorEliminationTraceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3db3RGeneratedInteriorEliminationTraceLedgerStatus
  sm3db2Ledger :
    SM3db2RGeneratedInteriorEliminationStepLedger b β p regularWeight variableWeight
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
  sm3db2Ledger_eq_main :
    sm3db2Ledger = sm3db2RGeneratedInteriorEliminationStepLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularTrace_eq_main :
    regularTrace = regularGeneratedInteriorEliminationTrace b p regularWeight
  variableTrace_eq_main :
    variableTrace = variableGeneratedInteriorEliminationTrace β p variableWeight
  regularTerminates :
    regularTrace.terminationStatus =
      SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier
  variableTerminates :
    variableTrace.terminationStatus =
      SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier
  regularSource_eq_SM3cR_SM3dR :
    regularTrace.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  variableSource_eq_SM3cR_SM3dR :
    variableTrace.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  regularNoExternalTraceOracle :
    regularTrace.noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  variableNoExternalTraceOracle :
    variableTrace.noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle
  regularNoInverseEntryFunction :
    regularTrace.noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R
  variableNoInverseEntryFunction :
    variableTrace.noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R
  regularNoMatrixExport :
    regularTrace.noMatrixExportStatus =
      SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R
  variableNoMatrixExport :
    variableTrace.noMatrixExportStatus =
      SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R
  regularNoTwoSidedInv :
    regularTrace.noTwoSidedInvStatus =
      SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R
  variableNoTwoSidedInv :
    variableTrace.noTwoSidedInvStatus =
      SM3db3RNoTwoSidedInvStatus.noTwoSidedInvInSM3db3R
  regularNextPositivePhase :
    regularTrace.nextPositivePhase =
      SM3db3RNextPositivePhase.sm3db4RGeneratedInteriorInverseCandidateEntry
  variableNextPositivePhase :
    variableTrace.nextPositivePhase =
      SM3db3RNextPositivePhase.sm3db4RGeneratedInteriorInverseCandidateEntry
  status_eq_closed :
    status =
      SM3db3RGeneratedInteriorEliminationTraceLedgerStatus.generatedInteriorEliminationTraceClosed

def sm3db3RGeneratedInteriorEliminationTraceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status :=
    SM3db3RGeneratedInteriorEliminationTraceLedgerStatus.generatedInteriorEliminationTraceClosed
  sm3db2Ledger :=
    sm3db2RGeneratedInteriorEliminationStepLedger b β p regularWeight variableWeight
      regularPivot variablePivot
  regularTrace := regularGeneratedInteriorEliminationTrace b p regularWeight
  variableTrace := variableGeneratedInteriorEliminationTrace β p variableWeight
  sm3db2Ledger_eq_main := by
    rfl
  regularTrace_eq_main := by
    rfl
  variableTrace_eq_main := by
    rfl
  regularTerminates := by
    rfl
  variableTerminates := by
    rfl
  regularSource_eq_SM3cR_SM3dR := by
    rfl
  variableSource_eq_SM3cR_SM3dR := by
    rfl
  regularNoExternalTraceOracle := by
    rfl
  variableNoExternalTraceOracle := by
    rfl
  regularNoInverseEntryFunction := by
    rfl
  variableNoInverseEntryFunction := by
    rfl
  regularNoMatrixExport := by
    rfl
  variableNoMatrixExport := by
    rfl
  regularNoTwoSidedInv := by
    rfl
  variableNoTwoSidedInv := by
    rfl
  regularNextPositivePhase := by
    rfl
  variableNextPositivePhase := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3db3RGeneratedInteriorEliminationTraceLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3db3RGeneratedInteriorEliminationTraceLedgerStatus.generatedInteriorEliminationTraceClosed := by
  rfl

theorem sm3db3RGeneratedInteriorEliminationTraceLedger_regularTerminates
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularTrace.terminationStatus =
      SM3db3RTerminationStatus.terminatesByFiniteInteriorCarrier := by
  rfl

theorem sm3db3RGeneratedInteriorEliminationTraceLedger_variableNoExternalTraceOracle
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).variableTrace.noExternalTraceOracleStatus =
      SM3db3RNoExternalTraceOracleStatus.noExternalTraceOracle := by
  rfl

theorem sm3db3RGeneratedInteriorEliminationTraceLedger_regularNoInverseEntryFunction
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularTrace.noInverseEntryFunctionStatus =
      SM3db3RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db3R := by
  rfl

theorem sm3db3RGeneratedInteriorEliminationTraceLedger_variableNoMatrixExport
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).variableTrace.noMatrixExportStatus =
      SM3db3RNoMatrixExportStatus.noMatrixExportInSM3db3R := by
  rfl

theorem sm3db3RGeneratedInteriorEliminationTraceLedger_regularNextPositivePhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db3RGeneratedInteriorEliminationTraceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularTrace.nextPositivePhase =
      SM3db3RNextPositivePhase.sm3db4RGeneratedInteriorInverseCandidateEntry := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
