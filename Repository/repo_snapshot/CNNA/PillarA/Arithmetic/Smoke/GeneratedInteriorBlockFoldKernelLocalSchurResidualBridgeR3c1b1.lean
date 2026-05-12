import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3c1b1BridgeStatus where
  | blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1KernelSourceStatus where
  | kernelSourceFromR3c1aBlockFoldNormalForm
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1LocalSchurResidualSourceStatus where
  | localSchurResidualFromSM3db2aRViaSM3db2fRScaleWitness
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoNewScaleStatus where
  | noNewScaleInBlockFoldKernelLocalSchurResidualBridge
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoNewReciprocalStatus where
  | noNewReciprocalInBlockFoldKernelLocalSchurResidualBridge
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoProductIdentityProofStatus where
  | noProductIdentityProofInBlockFoldKernelLocalSchurResidualBridge
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoTwoSidedInvStatus where
  | noTwoSidedInvInBlockFoldKernelLocalSchurResidualBridge
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInBlockFoldKernelLocalSchurResidualBridge
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInR3c1b1
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInR3c1b1
  deriving DecidableEq, Repr

inductive SM3eRr3c1b1NextPhaseStatus where
  | sm3eRr3c1bFullLocalStepCancellation
  deriving DecidableEq, Repr

def generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
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
    (pivot i j : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorLeftBlockFoldKernel W T i j pivot +
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (J.perPivotInvariant pivot).pivotScale i j

def generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
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
    (pivot i j : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorRightBlockFoldKernel W T i j pivot +
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (J.perPivotInvariant pivot).pivotScale i j

structure GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1
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
  operationalDegreeReciprocalSource :
    GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T
  tracePivotScaleWitness : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T
  perPivotRegularity : GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T
  traceLocalStepInvariant : GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T
  bridgeStatus : SM3eRr3c1b1BridgeStatus
  kernelSourceStatus : SM3eRr3c1b1KernelSourceStatus
  localSchurResidualSourceStatus : SM3eRr3c1b1LocalSchurResidualSourceStatus
  noNewScaleStatus : SM3eRr3c1b1NoNewScaleStatus
  noNewReciprocalStatus : SM3eRr3c1b1NoNewReciprocalStatus
  noProductIdentityProofStatus : SM3eRr3c1b1NoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1b1NoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3eRr3c1b1NoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRr3c1b1NoDtnDataStatus
  noArithmeticTargetStatus : SM3eRr3c1b1NoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1b1NextPhaseStatus
  blockFoldNormalForm_is_fromTrace :
    blockFoldNormalForm = GeneratedInteriorBlockFoldNormalFormR3c1a.fromEliminationTrace T
  tracePivotScaleWitness_eq_from_SM3db2fR :
    tracePivotScaleWitness =
      tracePivotScaleWitness_from_generatedOperationalDegreeReciprocalSourceSM3db2fR
        operationalDegreeReciprocalSource
  perPivotRegularity_eq_from_tracePivotScaleWitness :
    perPivotRegularity =
      GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR.fromTracePivotScaleWitness
        tracePivotScaleWitness
  traceLocalStepInvariant_eq_from_perPivotRegularity :
    traceLocalStepInvariant = perPivotRegularity.traceLocalStepInvariant
  leftKernel_eq_r3c1a_components :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldKernel W T i j pivot =
        generatedInteriorBlock W i pivot *
          (generatedInteriorTracePivotContribution T pivot j +
            generatedInteriorTraceLocalStepContribution T pivot j +
              generatedInteriorTraceResidualContribution T pivot j +
                generatedInteriorTraceFoldUpdateOrderContribution T pivot j)
  rightKernel_eq_r3c1a_components :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldKernel W T i j pivot =
        (generatedInteriorTracePivotContribution T i pivot +
            generatedInteriorTraceLocalStepContribution T i pivot +
              generatedInteriorTraceResidualContribution T i pivot +
                generatedInteriorTraceFoldUpdateOrderContribution T i pivot) *
          generatedInteriorBlock W pivot j
  leftLocalSchurResidual_eq_SM3db2aR :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual
        (T.localStepOf pivot) (traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j =
        generatedInteriorLocalSchurUpdateEquationResidual
          (T.localStepOf pivot) (traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j
  rightLocalSchurResidual_eq_SM3db2aR :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual
        (T.localStepOf pivot) (traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j =
        generatedInteriorLocalSchurUpdateEquationResidual
          (T.localStepOf pivot) (traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j
  leftLocalSchurResidual_eq_zero_from_SM3db2aR :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual
        (T.localStepOf pivot) (traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0
  rightLocalSchurResidual_eq_zero_from_SM3db2aR :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual
        (T.localStepOf pivot) (traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0
  leftKernelLocalSchurResidualBridge_eq_kernel :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T traceLocalStepInvariant pivot i j =
        generatedInteriorLeftBlockFoldKernel W T i j pivot
  rightKernelLocalSchurResidualBridge_eq_kernel :
    ∀ pivot i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
        W T traceLocalStepInvariant pivot i j =
        generatedInteriorRightBlockFoldKernel W T i j pivot
  bridgeStatus_eq :
    bridgeStatus =
      SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  kernelSourceStatus_eq :
    kernelSourceStatus =
      SM3eRr3c1b1KernelSourceStatus.kernelSourceFromR3c1aBlockFoldNormalForm
  localSchurResidualSourceStatus_eq :
    localSchurResidualSourceStatus =
      SM3eRr3c1b1LocalSchurResidualSourceStatus.localSchurResidualFromSM3db2aRViaSM3db2fRScaleWitness
  noNewScaleStatus_eq :
    noNewScaleStatus =
      SM3eRr3c1b1NoNewScaleStatus.noNewScaleInBlockFoldKernelLocalSchurResidualBridge
  noNewReciprocalStatus_eq :
    noNewReciprocalStatus =
      SM3eRr3c1b1NoNewReciprocalStatus.noNewReciprocalInBlockFoldKernelLocalSchurResidualBridge
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1b1NoProductIdentityProofStatus.noProductIdentityProofInBlockFoldKernelLocalSchurResidualBridge
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3eRr3c1b1NoTwoSidedInvStatus.noTwoSidedInvInBlockFoldKernelLocalSchurResidualBridge
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRr3c1b1NoInteriorEliminationDataStatus.noInteriorEliminationDataInBlockFoldKernelLocalSchurResidualBridge
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRr3c1b1NoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInR3c1b1
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRr3c1b1NoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInR3c1b1
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1b1NextPhaseStatus.sm3eRr3c1bFullLocalStepCancellation

namespace GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1

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

def fromOperationalDegreeReciprocalSource
    (S : GeneratedOperationalDegreeReciprocalSourceSM3db2fR Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T :=
  let N : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T :=
    GeneratedInteriorBlockFoldNormalFormR3c1a.fromEliminationTrace T
  let Q : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T :=
    tracePivotScaleWitness_from_generatedOperationalDegreeReciprocalSourceSM3db2fR S
  let R : GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T :=
    GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR.fromTracePivotScaleWitness Q
  let J : GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T :=
    R.traceLocalStepInvariant
  { blockFoldNormalForm := N
    operationalDegreeReciprocalSource := S
    tracePivotScaleWitness := Q
    perPivotRegularity := R
    traceLocalStepInvariant := J
    bridgeStatus :=
      SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
    kernelSourceStatus :=
      SM3eRr3c1b1KernelSourceStatus.kernelSourceFromR3c1aBlockFoldNormalForm
    localSchurResidualSourceStatus :=
      SM3eRr3c1b1LocalSchurResidualSourceStatus.localSchurResidualFromSM3db2aRViaSM3db2fRScaleWitness
    noNewScaleStatus :=
      SM3eRr3c1b1NoNewScaleStatus.noNewScaleInBlockFoldKernelLocalSchurResidualBridge
    noNewReciprocalStatus :=
      SM3eRr3c1b1NoNewReciprocalStatus.noNewReciprocalInBlockFoldKernelLocalSchurResidualBridge
    noProductIdentityProofStatus :=
      SM3eRr3c1b1NoProductIdentityProofStatus.noProductIdentityProofInBlockFoldKernelLocalSchurResidualBridge
    noTwoSidedInvStatus :=
      SM3eRr3c1b1NoTwoSidedInvStatus.noTwoSidedInvInBlockFoldKernelLocalSchurResidualBridge
    noInteriorEliminationDataStatus :=
      SM3eRr3c1b1NoInteriorEliminationDataStatus.noInteriorEliminationDataInBlockFoldKernelLocalSchurResidualBridge
    noDtnDataStatus :=
      SM3eRr3c1b1NoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInR3c1b1
    noArithmeticTargetStatus :=
      SM3eRr3c1b1NoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInR3c1b1
    nextPhaseStatus := SM3eRr3c1b1NextPhaseStatus.sm3eRr3c1bFullLocalStepCancellation
    blockFoldNormalForm_is_fromTrace := by
      rfl
    tracePivotScaleWitness_eq_from_SM3db2fR := by
      rfl
    perPivotRegularity_eq_from_tracePivotScaleWitness := by
      rfl
    traceLocalStepInvariant_eq_from_perPivotRegularity := by
      rfl
    leftKernel_eq_r3c1a_components := by
      intro pivot i j
      exact N.leftKernel_eq_components i j pivot
    rightKernel_eq_r3c1a_components := by
      intro pivot i j
      exact N.rightKernel_eq_components i j pivot
    leftLocalSchurResidual_eq_SM3db2aR := by
      intro pivot i j
      rfl
    rightLocalSchurResidual_eq_SM3db2aR := by
      intro pivot i j
      rfl
    leftLocalSchurResidual_eq_zero_from_SM3db2aR := by
      intro pivot i j
      exact (J.perPivotInvariant pivot).leftLocalStepCancellation i j
    rightLocalSchurResidual_eq_zero_from_SM3db2aR := by
      intro pivot i j
      exact (J.perPivotInvariant pivot).rightLocalStepCancellation i j
    leftKernelLocalSchurResidualBridge_eq_kernel := by
      intro pivot i j
      calc
        generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1 W T J pivot i j =
            generatedInteriorLeftBlockFoldKernel W T i j pivot +
              generatedInteriorLocalSchurUpdateEquationResidual
                (T.localStepOf pivot) (J.perPivotInvariant pivot).pivotScale i j := by
          rfl
        _ = generatedInteriorLeftBlockFoldKernel W T i j pivot + 0 := by
          exact congrArg
            (fun x => generatedInteriorLeftBlockFoldKernel W T i j pivot + x)
            ((J.perPivotInvariant pivot).leftLocalStepCancellation i j)
        _ = generatedInteriorLeftBlockFoldKernel W T i j pivot := by
          exact add_zero (generatedInteriorLeftBlockFoldKernel W T i j pivot)
    rightKernelLocalSchurResidualBridge_eq_kernel := by
      intro pivot i j
      calc
        generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1 W T J pivot i j =
            generatedInteriorRightBlockFoldKernel W T i j pivot +
              generatedInteriorLocalSchurUpdateEquationResidual
                (T.localStepOf pivot) (J.perPivotInvariant pivot).pivotScale i j := by
          rfl
        _ = generatedInteriorRightBlockFoldKernel W T i j pivot + 0 := by
          exact congrArg
            (fun x => generatedInteriorRightBlockFoldKernel W T i j pivot + x)
            ((J.perPivotInvariant pivot).rightLocalStepCancellation i j)
        _ = generatedInteriorRightBlockFoldKernel W T i j pivot := by
          exact add_zero (generatedInteriorRightBlockFoldKernel W T i j pivot)
    bridgeStatus_eq := by
      rfl
    kernelSourceStatus_eq := by
      rfl
    localSchurResidualSourceStatus_eq := by
      rfl
    noNewScaleStatus_eq := by
      rfl
    noNewReciprocalStatus_eq := by
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
      rfl }

theorem leftBridge_eq_kernel
    (B : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T B.traceLocalStepInvariant pivot i j =
      generatedInteriorLeftBlockFoldKernel W T i j pivot :=
  B.leftKernelLocalSchurResidualBridge_eq_kernel pivot i j

theorem rightBridge_eq_kernel
    (B : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFoldKernelLocalSchurResidualBridgeR3c1b1
      W T B.traceLocalStepInvariant pivot i j =
      generatedInteriorRightBlockFoldKernel W T i j pivot :=
  B.rightKernelLocalSchurResidualBridge_eq_kernel pivot i j

theorem leftLocalSchurResidual_eq_zero
    (B : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (B.traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0 :=
  B.leftLocalSchurResidual_eq_zero_from_SM3db2aR pivot i j

theorem rightLocalSchurResidual_eq_zero
    (B : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (B.traceLocalStepInvariant.perPivotInvariant pivot).pivotScale i j = 0 :=
  B.rightLocalSchurResidual_eq_zero_from_SM3db2aR pivot i j

theorem nextPhase_is_r3c1b_full
    (B : GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 Cell p A P wp W E K T) :
    B.nextPhaseStatus = SM3eRr3c1b1NextPhaseStatus.sm3eRr3c1bFullLocalStepCancellation :=
  B.nextPhaseStatus_eq

end GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1

abbrev RegularGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularBlockFoldKernelLocalSchurResidualBridgeR3c1b1
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p wp) :
    RegularGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 b p wp :=
  GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1.fromOperationalDegreeReciprocalSource S

def variableBlockFoldKernelLocalSchurResidualBridgeR3c1b1
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p wp) :
    VariableGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 β p wp :=
  GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1.fromOperationalDegreeReciprocalSource S

structure SM3eRr3c1b1BlockFoldKernelLocalSchurResidualBridgeLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularBridge : RegularGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 b p regularWeight
  variableBridge : VariableGeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1 β p variableWeight
  bridgeStatus : SM3eRr3c1b1BridgeStatus
  nextPhaseStatus : SM3eRr3c1b1NextPhaseStatus
  regularBridgeStatus_eq :
    regularBridge.bridgeStatus =
      SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  variableBridgeStatus_eq :
    variableBridge.bridgeStatus =
      SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  regularNoProductIdentityProofStatus_eq :
    regularBridge.noProductIdentityProofStatus =
      SM3eRr3c1b1NoProductIdentityProofStatus.noProductIdentityProofInBlockFoldKernelLocalSchurResidualBridge
  variableNoProductIdentityProofStatus_eq :
    variableBridge.noProductIdentityProofStatus =
      SM3eRr3c1b1NoProductIdentityProofStatus.noProductIdentityProofInBlockFoldKernelLocalSchurResidualBridge
  regularNoTwoSidedInvStatus_eq :
    regularBridge.noTwoSidedInvStatus =
      SM3eRr3c1b1NoTwoSidedInvStatus.noTwoSidedInvInBlockFoldKernelLocalSchurResidualBridge
  variableNoTwoSidedInvStatus_eq :
    variableBridge.noTwoSidedInvStatus =
      SM3eRr3c1b1NoTwoSidedInvStatus.noTwoSidedInvInBlockFoldKernelLocalSchurResidualBridge
  bridgeStatus_eq :
    bridgeStatus =
      SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1b1NextPhaseStatus.sm3eRr3c1bFullLocalStepCancellation

namespace SM3eRr3c1b1BlockFoldKernelLocalSchurResidualBridgeLedger

def fromRegularAndVariable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularSource : RegularGeneratedOperationalDegreeReciprocalSourceSM3db2fR b p regularWeight)
    (variableSource : VariableGeneratedOperationalDegreeReciprocalSourceSM3db2fR β p variableWeight) :
    SM3eRr3c1b1BlockFoldKernelLocalSchurResidualBridgeLedger
      b β p regularWeight variableWeight where
  regularBridge := regularBlockFoldKernelLocalSchurResidualBridgeR3c1b1 regularSource
  variableBridge := variableBlockFoldKernelLocalSchurResidualBridgeR3c1b1 variableSource
  bridgeStatus :=
    SM3eRr3c1b1BridgeStatus.blockFoldKernelLocalSchurResidualBridgeFromR3c1aAndSM3db2aR
  nextPhaseStatus := SM3eRr3c1b1NextPhaseStatus.sm3eRr3c1bFullLocalStepCancellation
  regularBridgeStatus_eq := by
    rfl
  variableBridgeStatus_eq := by
    rfl
  regularNoProductIdentityProofStatus_eq := by
    rfl
  variableNoProductIdentityProofStatus_eq := by
    rfl
  regularNoTwoSidedInvStatus_eq := by
    rfl
  variableNoTwoSidedInvStatus_eq := by
    rfl
  bridgeStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3eRr3c1b1BlockFoldKernelLocalSchurResidualBridgeLedger

end Smoke

end CNNA.PillarA.Arithmetic
