import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3c1bFullLocalStepCancellationStatus where
  | localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullBridgeSourceStatus where
  | sourceFromBlockFoldKernelLocalSchurResidualBridgeR3c1b1
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullLocalResidualSourceStatus where
  | sourceFromSM3db2aRTraceLocalStepCancellationInvariant
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoFoldInductionStatus where
  | noFoldInductionInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoTerminalIdentityStatus where
  | noTerminalCoverageOrIdentityGateInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoProductIdentityProofStatus where
  | noProductIdentityProofInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoTwoSidedInvStatus where
  | noTwoSidedInvInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInLocalStepCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1bFullNextPhaseStatus where
  | sm3eRr3c1cFoldInvariance
  deriving DecidableEq, Repr

structure GeneratedInteriorLocalStepCancellationR3c1bFull
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
  bridge : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T
  cancellationStatus : SM3eRr3c1bFullLocalStepCancellationStatus
  bridgeSourceStatus : SM3eRr3c1bFullBridgeSourceStatus
  localResidualSourceStatus : SM3eRr3c1bFullLocalResidualSourceStatus
  noFoldInductionStatus : SM3eRr3c1bFullNoFoldInductionStatus
  noTerminalIdentityStatus : SM3eRr3c1bFullNoTerminalIdentityStatus
  noProductIdentityProofStatus : SM3eRr3c1bFullNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1bFullNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3eRr3c1bFullNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRr3c1bFullNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRr3c1bFullNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1bFullNextPhaseStatus
  bridgeStatus_eq_r3c1b1 :
    bridge.bridgeStatus =
      SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  bridgeNextPhase_eq_r3c1b_full :
    bridge.nextPhaseStatus = SM3eRr3c1b1NextPhaseStatus.sm3eRr3c1bFullLocalStepCancellation
  leftLocalSchurResidual_eq_zero_consumed :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual
        (T.localStepOf pivot) (bridge.traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0
  rightLocalSchurResidual_eq_zero_consumed :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual
        (T.localStepOf pivot) (bridge.traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0
  leftBridge_eq_kernel_from_residual_zero :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T bridge.traceLocalStepInvariant pivot i j =
        generatedInteriorLeftBlockFoldKernel W T i j pivot
  rightBridge_eq_kernel_from_residual_zero :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T bridge.traceLocalStepInvariant pivot i j =
        generatedInteriorRightBlockFoldKernel W T i j pivot
  leftLocalStepCancellation_from_bridge :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T bridge.traceLocalStepInvariant pivot i j -
        generatedInteriorLeftBlockFoldKernel W T i j pivot = 0
  rightLocalStepCancellation_from_bridge :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T bridge.traceLocalStepInvariant pivot i j -
        generatedInteriorRightBlockFoldKernel W T i j pivot = 0
  cancellationStatus_eq :
    cancellationStatus =
      SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  bridgeSourceStatus_eq :
    bridgeSourceStatus =
      SM3eRr3c1bFullBridgeSourceStatus.sourceFromBlockFoldKernelLocalSchurResidualBridgeR3c1b1
  localResidualSourceStatus_eq :
    localResidualSourceStatus =
      SM3eRr3c1bFullLocalResidualSourceStatus.sourceFromSM3db2aRTraceLocalStepCancellationInvariant
  noFoldInductionStatus_eq :
    noFoldInductionStatus = SM3eRr3c1bFullNoFoldInductionStatus.noFoldInductionInLocalStepCancellation
  noTerminalIdentityStatus_eq :
    noTerminalIdentityStatus =
      SM3eRr3c1bFullNoTerminalIdentityStatus.noTerminalCoverageOrIdentityGateInLocalStepCancellation
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1bFullNoProductIdentityProofStatus.noProductIdentityProofInLocalStepCancellation
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRr3c1bFullNoTwoSidedInvStatus.noTwoSidedInvInLocalStepCancellation
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRr3c1bFullNoInteriorEliminationDataStatus.noInteriorEliminationDataInLocalStepCancellation
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRr3c1bFullNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInLocalStepCancellation
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRr3c1bFullNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInLocalStepCancellation
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1bFullNextPhaseStatus.sm3eRr3c1cFoldInvariance

namespace GeneratedInteriorLocalStepCancellationR3c1bFull

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

def fromBridge
    (B : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T) :
    GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T where
  bridge := B
  cancellationStatus :=
    SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  bridgeSourceStatus :=
    SM3eRr3c1bFullBridgeSourceStatus.sourceFromBlockFoldKernelLocalSchurResidualBridgeR3c1b1
  localResidualSourceStatus :=
    SM3eRr3c1bFullLocalResidualSourceStatus.sourceFromSM3db2aRTraceLocalStepCancellationInvariant
  noFoldInductionStatus :=
    SM3eRr3c1bFullNoFoldInductionStatus.noFoldInductionInLocalStepCancellation
  noTerminalIdentityStatus :=
    SM3eRr3c1bFullNoTerminalIdentityStatus.noTerminalCoverageOrIdentityGateInLocalStepCancellation
  noProductIdentityProofStatus :=
    SM3eRr3c1bFullNoProductIdentityProofStatus.noProductIdentityProofInLocalStepCancellation
  noTwoSidedInvStatus := SM3eRr3c1bFullNoTwoSidedInvStatus.noTwoSidedInvInLocalStepCancellation
  noInteriorEliminationDataStatus :=
    SM3eRr3c1bFullNoInteriorEliminationDataStatus.noInteriorEliminationDataInLocalStepCancellation
  noDtnDataStatus :=
    SM3eRr3c1bFullNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInLocalStepCancellation
  noArithmeticTargetStatus :=
    SM3eRr3c1bFullNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInLocalStepCancellation
  nextPhaseStatus := SM3eRr3c1bFullNextPhaseStatus.sm3eRr3c1cFoldInvariance
  bridgeStatus_eq_r3c1b1 := B.bridgeStatus_eq
  bridgeNextPhase_eq_r3c1b_full := B.nextPhaseStatus_eq
  leftLocalSchurResidual_eq_zero_consumed := by
    intro pivot i j
    exact B.leftLocalSchurResidual_eq_zero_from_SM3db2aR pivot i j
  rightLocalSchurResidual_eq_zero_consumed := by
    intro pivot i j
    exact B.rightLocalSchurResidual_eq_zero_from_SM3db2aR pivot i j
  leftBridge_eq_kernel_from_residual_zero := by
    intro pivot i j
    exact B.leftKernelLocalSchurResidualBridge_eq_kernel pivot i j
  rightBridge_eq_kernel_from_residual_zero := by
    intro pivot i j
    exact B.rightKernelLocalSchurResidualBridge_eq_kernel pivot i j
  leftLocalStepCancellation_from_bridge := by
    intro pivot i j
    calc
      generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
            W T B.traceLocalStepInvariant pivot i j -
          generatedInteriorLeftBlockFoldKernel W T i j pivot =
          generatedInteriorLeftBlockFoldKernel W T i j pivot -
            generatedInteriorLeftBlockFoldKernel W T i j pivot := by
        exact congrArg
          (fun x => x - generatedInteriorLeftBlockFoldKernel W T i j pivot)
          (B.leftKernelLocalSchurResidualBridge_eq_kernel pivot i j)
      _ = 0 := by
        exact sub_self (generatedInteriorLeftBlockFoldKernel W T i j pivot)
  rightLocalStepCancellation_from_bridge := by
    intro pivot i j
    calc
      generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
            W T B.traceLocalStepInvariant pivot i j -
          generatedInteriorRightBlockFoldKernel W T i j pivot =
          generatedInteriorRightBlockFoldKernel W T i j pivot -
            generatedInteriorRightBlockFoldKernel W T i j pivot := by
        exact congrArg
          (fun x => x - generatedInteriorRightBlockFoldKernel W T i j pivot)
          (B.rightKernelLocalSchurResidualBridge_eq_kernel pivot i j)
      _ = 0 := by
        exact sub_self (generatedInteriorRightBlockFoldKernel W T i j pivot)
  cancellationStatus_eq := by
    rfl
  bridgeSourceStatus_eq := by
    rfl
  localResidualSourceStatus_eq := by
    rfl
  noFoldInductionStatus_eq := by
    rfl
  noTerminalIdentityStatus_eq := by
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
    GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T :=
  fromBridge (GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1.fromOperationalDegreeReciprocalSource S)

theorem leftLocalSchurResidual_eq_zero
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (C.bridge.traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0 :=
  C.leftLocalSchurResidual_eq_zero_consumed pivot i j

theorem rightLocalSchurResidual_eq_zero
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (C.bridge.traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0 :=
  C.rightLocalSchurResidual_eq_zero_consumed pivot i j

theorem leftBridge_eq_kernel
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T C.bridge.traceLocalStepInvariant pivot i j =
      generatedInteriorLeftBlockFoldKernel W T i j pivot :=
  C.leftBridge_eq_kernel_from_residual_zero pivot i j

theorem rightBridge_eq_kernel
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T C.bridge.traceLocalStepInvariant pivot i j =
      generatedInteriorRightBlockFoldKernel W T i j pivot :=
  C.rightBridge_eq_kernel_from_residual_zero pivot i j

theorem leftLocalStepCancellation
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T C.bridge.traceLocalStepInvariant pivot i j -
      generatedInteriorLeftBlockFoldKernel W T i j pivot = 0 :=
  C.leftLocalStepCancellation_from_bridge pivot i j

theorem rightLocalStepCancellation
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T C.bridge.traceLocalStepInvariant pivot i j -
      generatedInteriorRightBlockFoldKernel W T i j pivot = 0 :=
  C.rightLocalStepCancellation_from_bridge pivot i j

theorem nextPhase_is_r3c1c
    (C : GeneratedInteriorLocalStepCancellationR3c1bFull Cell p A P wp W E K T) :
    C.nextPhaseStatus = SM3eRr3c1bFullNextPhaseStatus.sm3eRr3c1cFoldInvariance :=
  C.nextPhaseStatus_eq

end GeneratedInteriorLocalStepCancellationR3c1bFull

abbrev RegularGeneratedInteriorLocalStepCancellationR3c1bFull
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorLocalStepCancellationR3c1bFull
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorLocalStepCancellationR3c1bFull
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorLocalStepCancellationR3c1bFull
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularLocalStepCancellationR3c1bFull
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (B : RegularGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 b p wp) :
    RegularGeneratedInteriorLocalStepCancellationR3c1bFull b p wp :=
  GeneratedInteriorLocalStepCancellationR3c1bFull.fromBridge B

def variableLocalStepCancellationR3c1bFull
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (B : VariableGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 β p wp) :
    VariableGeneratedInteriorLocalStepCancellationR3c1bFull β p wp :=
  GeneratedInteriorLocalStepCancellationR3c1bFull.fromBridge B

def regularLocalStepCancellationR3c1bFullFromOperationalDegreeReciprocalSource
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p wp) :
    RegularGeneratedInteriorLocalStepCancellationR3c1bFull b p wp :=
  GeneratedInteriorLocalStepCancellationR3c1bFull.fromOperationalDegreeReciprocalSource S

def variableLocalStepCancellationR3c1bFullFromOperationalDegreeReciprocalSource
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p wp) :
    VariableGeneratedInteriorLocalStepCancellationR3c1bFull β p wp :=
  GeneratedInteriorLocalStepCancellationR3c1bFull.fromOperationalDegreeReciprocalSource S

structure SM3eRr3c1bFullLocalStepCancellationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularCancellation : RegularGeneratedInteriorLocalStepCancellationR3c1bFull b p regularWeight
  variableCancellation : VariableGeneratedInteriorLocalStepCancellationR3c1bFull β p variableWeight
  cancellationStatus : SM3eRr3c1bFullLocalStepCancellationStatus
  nextPhaseStatus : SM3eRr3c1bFullNextPhaseStatus
  regularCancellationStatus_eq :
    regularCancellation.cancellationStatus =
      SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  variableCancellationStatus_eq :
    variableCancellation.cancellationStatus =
      SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  regularNoFoldInductionStatus_eq :
    regularCancellation.noFoldInductionStatus =
      SM3eRr3c1bFullNoFoldInductionStatus.noFoldInductionInLocalStepCancellation
  variableNoFoldInductionStatus_eq :
    variableCancellation.noFoldInductionStatus =
      SM3eRr3c1bFullNoFoldInductionStatus.noFoldInductionInLocalStepCancellation
  regularNoTerminalIdentityStatus_eq :
    regularCancellation.noTerminalIdentityStatus =
      SM3eRr3c1bFullNoTerminalIdentityStatus.noTerminalCoverageOrIdentityGateInLocalStepCancellation
  variableNoTerminalIdentityStatus_eq :
    variableCancellation.noTerminalIdentityStatus =
      SM3eRr3c1bFullNoTerminalIdentityStatus.noTerminalCoverageOrIdentityGateInLocalStepCancellation
  regularNoProductIdentityProofStatus_eq :
    regularCancellation.noProductIdentityProofStatus =
      SM3eRr3c1bFullNoProductIdentityProofStatus.noProductIdentityProofInLocalStepCancellation
  variableNoProductIdentityProofStatus_eq :
    variableCancellation.noProductIdentityProofStatus =
      SM3eRr3c1bFullNoProductIdentityProofStatus.noProductIdentityProofInLocalStepCancellation
  regularNoTwoSidedInvStatus_eq :
    regularCancellation.noTwoSidedInvStatus =
      SM3eRr3c1bFullNoTwoSidedInvStatus.noTwoSidedInvInLocalStepCancellation
  variableNoTwoSidedInvStatus_eq :
    variableCancellation.noTwoSidedInvStatus =
      SM3eRr3c1bFullNoTwoSidedInvStatus.noTwoSidedInvInLocalStepCancellation
  cancellationStatus_eq :
    cancellationStatus =
      SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1bFullNextPhaseStatus.sm3eRr3c1cFoldInvariance

namespace SM3eRr3c1bFullLocalStepCancellationLedger

def fromRegularAndVariableBridges
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularBridge : RegularGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 b p regularWeight)
    (variableBridge : VariableGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 β p variableWeight) :
    SM3eRr3c1bFullLocalStepCancellationLedger b β p regularWeight variableWeight where
  regularCancellation := regularLocalStepCancellationR3c1bFull regularBridge
  variableCancellation := variableLocalStepCancellationR3c1bFull variableBridge
  cancellationStatus :=
    SM3eRr3c1bFullLocalStepCancellationStatus.localStepCancellationFromR3c1b1BridgeAndSM3db2aRResidualZero
  nextPhaseStatus := SM3eRr3c1bFullNextPhaseStatus.sm3eRr3c1cFoldInvariance
  regularCancellationStatus_eq := by
    rfl
  variableCancellationStatus_eq := by
    rfl
  regularNoFoldInductionStatus_eq := by
    rfl
  variableNoFoldInductionStatus_eq := by
    rfl
  regularNoTerminalIdentityStatus_eq := by
    rfl
  variableNoTerminalIdentityStatus_eq := by
    rfl
  regularNoProductIdentityProofStatus_eq := by
    rfl
  variableNoProductIdentityProofStatus_eq := by
    rfl
  regularNoTwoSidedInvStatus_eq := by
    rfl
  variableNoTwoSidedInvStatus_eq := by
    rfl
  cancellationStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromOperationalDegreeReciprocalSources
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularSource : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p regularWeight)
    (variableSource : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p variableWeight) :
    SM3eRr3c1bFullLocalStepCancellationLedger b β p regularWeight variableWeight :=
  fromRegularAndVariableBridges
    (regularBlockFoldKernelLocalSchurResidualBridgeR3c1b1 regularSource)
    (variableBlockFoldKernelLocalSchurResidualBridgeR3c1b1 variableSource)

end SM3eRr3c1bFullLocalStepCancellationLedger

end Smoke

end CNNA.PillarA.Arithmetic
