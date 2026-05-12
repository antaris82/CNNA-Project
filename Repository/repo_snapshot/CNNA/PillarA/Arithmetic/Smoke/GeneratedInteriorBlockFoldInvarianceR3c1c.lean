import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

open scoped BigOperators

namespace Smoke

universe u

inductive SM3eRr3c1cFoldInvarianceStatus where
  | foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  deriving DecidableEq, Repr

inductive SM3eRr3c1cBlockFoldNormalFormSourceStatus where
  | sourceFromR3c1aBlockFoldNormalForm
  deriving DecidableEq, Repr

inductive SM3eRr3c1cLocalStepCancellationSourceStatus where
  | sourceFromR3c1bFullLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1cTraceFoldSourceStatus where
  | sourceFromSM3db3RTraceAndSM3db4aRFold
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoTerminalIdentityStatus where
  | noTerminalIdentityInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoAccumulatedEntryCancellationStatus where
  | noAccumulatedEntryCancellationInvariantInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoProductIdentityProofStatus where
  | noProductIdentityProofInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoTwoSidedInvStatus where
  | noTwoSidedInvInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInFoldInvariance
  deriving DecidableEq, Repr

inductive SM3eRr3c1cNextPhaseStatus where
  | sm3eRr3c1dTerminalIdentity
  deriving DecidableEq, Repr

def generatedInteriorLeftBlockFoldStepSourceR3c1c
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (J : GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ pivot : GeneratedInteriorIndex A,
    generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T J pivot i j

def generatedInteriorRightBlockFoldStepSourceR3c1c
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (J : GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ pivot : GeneratedInteriorIndex A,
    generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T J pivot i j

structure GeneratedInteriorBlockFoldInvarianceR3c1c
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
  blockFoldNormalForm : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T
  localStepCancellation : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T
  invarianceStatus : SM3eRr3c1cFoldInvarianceStatus
  blockFoldNormalFormSourceStatus : SM3eRr3c1cBlockFoldNormalFormSourceStatus
  localStepCancellationSourceStatus : SM3eRr3c1cLocalStepCancellationSourceStatus
  traceFoldSourceStatus : SM3eRr3c1cTraceFoldSourceStatus
  noTerminalIdentityStatus : SM3eRr3c1cNoTerminalIdentityStatus
  noAccumulatedEntryCancellationStatus : SM3eRr3c1cNoAccumulatedEntryCancellationStatus
  noProductIdentityProofStatus : SM3eRr3c1cNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1cNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3eRr3c1cNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRr3c1cNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRr3c1cNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1cNextPhaseStatus
  blockFoldNormalForm_eq_localStepSource :
    blockFoldNormalForm = localStepCancellation.bridge.blockFoldNormalForm
  localStepCancellation_bridgeSourceStatus_eq :
    localStepCancellation.bridgeSourceStatus =
      SM3eRr3c1bFullBridgeSourceStatus.sourceFromBlockFoldKernelLocalSchurResidualBridgeR3c1b1
  localStepCancellation_status_eq :
    localStepCancellation.cancellationStatus =
      SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    blockFoldNormalForm.accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    blockFoldNormalForm.accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  leftStepPreservation :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T localStepCancellation.bridge.traceLocalStepInvariant pivot i j =
        generatedInteriorLeftBlockFoldKernel W T i j pivot
  rightStepPreservation :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T localStepCancellation.bridge.traceLocalStepInvariant pivot i j =
        generatedInteriorRightBlockFoldKernel W T i j pivot
  leftFoldSumPreservation :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldStepSourceR3c1c
        W T localStepCancellation.bridge.traceLocalStepInvariant i j =
        generatedInteriorLeftBlockFold W T i j
  rightFoldSumPreservation :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldStepSourceR3c1c
        W T localStepCancellation.bridge.traceLocalStepInvariant i j =
        generatedInteriorRightBlockFold W T i j
  invarianceStatus_eq :
    invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  blockFoldNormalFormSourceStatus_eq :
    blockFoldNormalFormSourceStatus =
      SM3eRr3c1cBlockFoldNormalFormSourceStatus.sourceFromR3c1aBlockFoldNormalForm
  localStepCancellationSourceStatus_eq :
    localStepCancellationSourceStatus =
      SM3eRr3c1cLocalStepCancellationSourceStatus.sourceFromR3c1bFullLocalStepCancellation
  traceFoldSourceStatus_eq :
    traceFoldSourceStatus =
      SM3eRr3c1cTraceFoldSourceStatus.sourceFromSM3db3RTraceAndSM3db4aRFold
  noTerminalIdentityStatus_eq :
    noTerminalIdentityStatus =
      SM3eRr3c1cNoTerminalIdentityStatus.noTerminalIdentityInFoldInvariance
  noAccumulatedEntryCancellationStatus_eq :
    noAccumulatedEntryCancellationStatus =
      SM3eRr3c1cNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInFoldInvariance
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1cNoProductIdentityProofStatus.noProductIdentityProofInFoldInvariance
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRr3c1cNoTwoSidedInvStatus.noTwoSidedInvInFoldInvariance
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRr3c1cNoInteriorEliminationDataStatus.noInteriorEliminationDataInFoldInvariance
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRr3c1cNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInFoldInvariance
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRr3c1cNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInFoldInvariance
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1cNextPhaseStatus.sm3eRr3c1dTerminalIdentity

namespace GeneratedInteriorBlockFoldInvarianceR3c1c

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

def fromLocalStepCancellation
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T where
  blockFoldNormalForm := C.bridge.blockFoldNormalForm
  localStepCancellation := C
  invarianceStatus :=
    SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  blockFoldNormalFormSourceStatus :=
    SM3eRr3c1cBlockFoldNormalFormSourceStatus.sourceFromR3c1aBlockFoldNormalForm
  localStepCancellationSourceStatus :=
    SM3eRr3c1cLocalStepCancellationSourceStatus.sourceFromR3c1bFullLocalStepCancellation
  traceFoldSourceStatus :=
    SM3eRr3c1cTraceFoldSourceStatus.sourceFromSM3db3RTraceAndSM3db4aRFold
  noTerminalIdentityStatus :=
    SM3eRr3c1cNoTerminalIdentityStatus.noTerminalIdentityInFoldInvariance
  noAccumulatedEntryCancellationStatus :=
    SM3eRr3c1cNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInFoldInvariance
  noProductIdentityProofStatus :=
    SM3eRr3c1cNoProductIdentityProofStatus.noProductIdentityProofInFoldInvariance
  noTwoSidedInvStatus := SM3eRr3c1cNoTwoSidedInvStatus.noTwoSidedInvInFoldInvariance
  noInteriorEliminationDataStatus :=
    SM3eRr3c1cNoInteriorEliminationDataStatus.noInteriorEliminationDataInFoldInvariance
  noDtnDataStatus :=
    SM3eRr3c1cNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInFoldInvariance
  noArithmeticTargetStatus :=
    SM3eRr3c1cNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInFoldInvariance
  nextPhaseStatus := SM3eRr3c1cNextPhaseStatus.sm3eRr3c1dTerminalIdentity
  blockFoldNormalForm_eq_localStepSource := by
    rfl
  localStepCancellation_bridgeSourceStatus_eq :=
    C.bridgeSourceStatus_eq
  localStepCancellation_status_eq :=
    C.cancellationStatus_eq
  trace_source_eq_SM3db3R :=
    C.bridge.blockFoldNormalForm.trace_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    C.bridge.blockFoldNormalForm.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    C.bridge.blockFoldNormalForm.accumulatedFoldSource_eq_SM3db4aR
  leftStepPreservation := by
    intro pivot i j
    exact C.leftBridge_eq_kernel_from_residual_zero pivot i j
  rightStepPreservation := by
    intro pivot i j
    exact C.rightBridge_eq_kernel_from_residual_zero pivot i j
  leftFoldSumPreservation := by
    intro i j
    calc
      generatedInteriorLeftBlockFoldStepSourceR3c1c W T C.bridge.traceLocalStepInvariant i j =
          ∑ pivot : GeneratedInteriorIndex A,
            generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
              W T C.bridge.traceLocalStepInvariant pivot i j := by
        rfl
      _ = ∑ pivot : GeneratedInteriorIndex A,
            generatedInteriorLeftBlockFoldKernel W T i j pivot := by
        refine Finset.sum_congr rfl ?_
        intro pivot _
        exact C.leftBridge_eq_kernel_from_residual_zero pivot i j
      _ = generatedInteriorLeftBlockFold W T i j := by
        exact (C.bridge.blockFoldNormalForm.leftBlockFold_eq_kernelSum i j).symm
  rightFoldSumPreservation := by
    intro i j
    calc
      generatedInteriorRightBlockFoldStepSourceR3c1c W T C.bridge.traceLocalStepInvariant i j =
          ∑ pivot : GeneratedInteriorIndex A,
            generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
              W T C.bridge.traceLocalStepInvariant pivot i j := by
        rfl
      _ = ∑ pivot : GeneratedInteriorIndex A,
            generatedInteriorRightBlockFoldKernel W T i j pivot := by
        refine Finset.sum_congr rfl ?_
        intro pivot _
        exact C.rightBridge_eq_kernel_from_residual_zero pivot i j
      _ = generatedInteriorRightBlockFold W T i j := by
        exact (C.bridge.blockFoldNormalForm.rightBlockFold_eq_kernelSum i j).symm
  invarianceStatus_eq := by
    rfl
  blockFoldNormalFormSourceStatus_eq := by
    rfl
  localStepCancellationSourceStatus_eq := by
    rfl
  traceFoldSourceStatus_eq := by
    rfl
  noTerminalIdentityStatus_eq := by
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

def fromOperationalDegreeReciprocalSource
    (S : GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T :=
  fromLocalStepCancellation
    (GeneratedInteriorLocalStepCancellationR3c1bFull.fromOperationalDegreeReciprocalSource S)

theorem leftStepPreservesKernel
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T I.localStepCancellation.bridge.traceLocalStepInvariant pivot i j =
      generatedInteriorLeftBlockFoldKernel W T i j pivot :=
  I.leftStepPreservation pivot i j

theorem rightStepPreservesKernel
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T I.localStepCancellation.bridge.traceLocalStepInvariant pivot i j =
      generatedInteriorRightBlockFoldKernel W T i j pivot :=
  I.rightStepPreservation pivot i j

theorem leftFoldSum_eq_blockFold
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFoldStepSourceR3c1c
      W T I.localStepCancellation.bridge.traceLocalStepInvariant i j =
      generatedInteriorLeftBlockFold W T i j :=
  I.leftFoldSumPreservation i j

theorem rightFoldSum_eq_blockFold
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFoldStepSourceR3c1c
      W T I.localStepCancellation.bridge.traceLocalStepInvariant i j =
      generatedInteriorRightBlockFold W T i j :=
  I.rightFoldSumPreservation i j

theorem noTerminalIdentity
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    I.noTerminalIdentityStatus =
      SM3eRr3c1cNoTerminalIdentityStatus.noTerminalIdentityInFoldInvariance :=
  I.noTerminalIdentityStatus_eq

theorem noAccumulatedEntryCancellationInvariant
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    I.noAccumulatedEntryCancellationStatus =
      SM3eRr3c1cNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInFoldInvariance :=
  I.noAccumulatedEntryCancellationStatus_eq

theorem nextPhase_is_r3c1d
    (I : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T) :
    I.nextPhaseStatus = SM3eRr3c1cNextPhaseStatus.sm3eRr3c1dTerminalIdentity :=
  I.nextPhaseStatus_eq

end GeneratedInteriorBlockFoldInvarianceR3c1c

abbrev RegularGeneratedInteriorBlockFoldInvarianceR3c1c
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldInvarianceR3c1c
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorBlockFoldInvarianceR3c1c
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldInvarianceR3c1c
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularBlockFoldInvarianceR3c1c
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : RegularGeneratedInteriorLocalStepCancellationR3c1bFull b p wp) :
    RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p wp :=
  GeneratedInteriorBlockFoldInvarianceR3c1c.fromLocalStepCancellation C

def variableBlockFoldInvarianceR3c1c
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (C : VariableGeneratedInteriorLocalStepCancellationR3c1bFull β p wp) :
    VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p wp :=
  GeneratedInteriorBlockFoldInvarianceR3c1c.fromLocalStepCancellation C

def regularBlockFoldInvarianceR3c1cFromOperationalDegreeReciprocalSource
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p wp) :
    RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p wp :=
  GeneratedInteriorBlockFoldInvarianceR3c1c.fromOperationalDegreeReciprocalSource S

def variableBlockFoldInvarianceR3c1cFromOperationalDegreeReciprocalSource
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p wp) :
    VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p wp :=
  GeneratedInteriorBlockFoldInvarianceR3c1c.fromOperationalDegreeReciprocalSource S

structure SM3eRr3c1cBlockFoldInvarianceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularInvariance : RegularGeneratedInteriorBlockFoldInvarianceR3c1c b p regularWeight
  variableInvariance : VariableGeneratedInteriorBlockFoldInvarianceR3c1c β p variableWeight
  invarianceStatus : SM3eRr3c1cFoldInvarianceStatus
  nextPhaseStatus : SM3eRr3c1cNextPhaseStatus
  regularInvarianceStatus_eq :
    regularInvariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  variableInvarianceStatus_eq :
    variableInvariance.invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  regularNoTerminalIdentityStatus_eq :
    regularInvariance.noTerminalIdentityStatus =
      SM3eRr3c1cNoTerminalIdentityStatus.noTerminalIdentityInFoldInvariance
  variableNoTerminalIdentityStatus_eq :
    variableInvariance.noTerminalIdentityStatus =
      SM3eRr3c1cNoTerminalIdentityStatus.noTerminalIdentityInFoldInvariance
  regularNoAccumulatedEntryCancellationStatus_eq :
    regularInvariance.noAccumulatedEntryCancellationStatus =
      SM3eRr3c1cNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInFoldInvariance
  variableNoAccumulatedEntryCancellationStatus_eq :
    variableInvariance.noAccumulatedEntryCancellationStatus =
      SM3eRr3c1cNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInFoldInvariance
  regularNoProductIdentityProofStatus_eq :
    regularInvariance.noProductIdentityProofStatus =
      SM3eRr3c1cNoProductIdentityProofStatus.noProductIdentityProofInFoldInvariance
  variableNoProductIdentityProofStatus_eq :
    variableInvariance.noProductIdentityProofStatus =
      SM3eRr3c1cNoProductIdentityProofStatus.noProductIdentityProofInFoldInvariance
  regularNoTwoSidedInvStatus_eq :
    regularInvariance.noTwoSidedInvStatus =
      SM3eRr3c1cNoTwoSidedInvStatus.noTwoSidedInvInFoldInvariance
  variableNoTwoSidedInvStatus_eq :
    variableInvariance.noTwoSidedInvStatus =
      SM3eRr3c1cNoTwoSidedInvStatus.noTwoSidedInvInFoldInvariance
  invarianceStatus_eq :
    invarianceStatus =
      SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1cNextPhaseStatus.sm3eRr3c1dTerminalIdentity

namespace SM3eRr3c1cBlockFoldInvarianceLedger

def fromRegularAndVariableCancellations
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularCancellation : RegularGeneratedInteriorLocalStepCancellationR3c1bFull b p regularWeight)
    (variableCancellation : VariableGeneratedInteriorLocalStepCancellationR3c1bFull β p variableWeight) :
    SM3eRr3c1cBlockFoldInvarianceLedger b β p regularWeight variableWeight where
  regularInvariance := regularBlockFoldInvarianceR3c1c regularCancellation
  variableInvariance := variableBlockFoldInvarianceR3c1c variableCancellation
  invarianceStatus :=
    SM3eRr3c1cFoldInvarianceStatus.foldInvarianceFromR3c1aR3c1b1AndR3c1bFull
  nextPhaseStatus := SM3eRr3c1cNextPhaseStatus.sm3eRr3c1dTerminalIdentity
  regularInvarianceStatus_eq := by
    rfl
  variableInvarianceStatus_eq := by
    rfl
  regularNoTerminalIdentityStatus_eq := by
    rfl
  variableNoTerminalIdentityStatus_eq := by
    rfl
  regularNoAccumulatedEntryCancellationStatus_eq := by
    rfl
  variableNoAccumulatedEntryCancellationStatus_eq := by
    rfl
  regularNoProductIdentityProofStatus_eq := by
    rfl
  variableNoProductIdentityProofStatus_eq := by
    rfl
  regularNoTwoSidedInvStatus_eq := by
    rfl
  variableNoTwoSidedInvStatus_eq := by
    rfl
  invarianceStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromOperationalDegreeReciprocalSources
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularSource : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p regularWeight)
    (variableSource : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p variableWeight) :
    SM3eRr3c1cBlockFoldInvarianceLedger b β p regularWeight variableWeight :=
  fromRegularAndVariableCancellations
    (regularLocalStepCancellationR3c1bFullFromOperationalDegreeReciprocalSource regularSource)
    (variableLocalStepCancellationR3c1bFullFromOperationalDegreeReciprocalSource variableSource)

end SM3eRr3c1cBlockFoldInvarianceLedger

end Smoke

end CNNA.PillarA.Arithmetic
