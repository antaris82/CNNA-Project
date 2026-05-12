import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e
import CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u v

inductive SM9fFullDeterminantForwardBridgeStatus where
  | determinantForwardBridgeClosedFromSM9ePlusSource
  deriving DecidableEq, Repr

inductive SM9fFullNextPhaseStatus where
  | discriminantFactorGateAfterForwardBridge
  deriving DecidableEq, Repr

inductive SM9fFullOldEvalOrientationPatchStatus where
  | oldEvalOrientationNotUsedAsBridgeInput
  deriving DecidableEq, Repr

inductive SM9fFullNoNewForwardAlgebraStatus where
  | noNewForwardAlgebraLayer
  deriving DecidableEq, Repr

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedBoundaryIndex A)]
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
variable {G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H}

structure GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) where
  sourceSM9fRequirement : GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
    Cell p A P wp W E K T M S H G
  sourceSM9ePlus1 : GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
    Cell p A P wp W E K T M S H G
  sourceSM9ePlus1_nextPhase_eq_SM9fFull :
    sourceSM9ePlus1.nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  sourceSM9ePlus1_forwardStatus_eq :
    sourceSM9ePlus1.forwardEvaluationStatus =
      SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  forwardEvaluationAtSource : ExecComplex
  forwardEvaluationAtSource_eq_SM9dEvaluationAtSource :
    forwardEvaluationAtSource = sourceSM9fRequirement.sourceSM9e.sourceSM9d.evaluationAtSource
  forwardEvaluationAtSource_eq_SM9cEvaluationFamilyAtSource :
    forwardEvaluationAtSource =
      sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.evaluationFamily
        sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceParameter
  forwardEvaluationAtSource_eq_SM9cDetPencilAtSource :
    forwardEvaluationAtSource =
      Matrix.det sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  linearPencilForwardTarget_closed :
    ∀ {ι : Type v} [DecidableEq ι]
      (B : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
          (operationalLinearPencilEntryPolynomialSM9e 1 B i j) z =
        (-(B i j)) +
          Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0)
  forwardEvaluationTargetStatement : Prop
  forwardEvaluationTargetStatement_eq :
    forwardEvaluationTargetStatement =
      operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus1
  bridgeStatus : SM9fFullDeterminantForwardBridgeStatus
  bridgeStatus_eq :
    bridgeStatus =
      SM9fFullDeterminantForwardBridgeStatus.determinantForwardBridgeClosedFromSM9ePlusSource
  nextPhaseStatus : SM9fFullNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9fFullNextPhaseStatus.discriminantFactorGateAfterForwardBridge
  oldEvalOrientationPatchStatus : SM9fFullOldEvalOrientationPatchStatus
  oldEvalOrientationPatchStatus_eq :
    oldEvalOrientationPatchStatus =
      SM9fFullOldEvalOrientationPatchStatus.oldEvalOrientationNotUsedAsBridgeInput
  noNewForwardAlgebraStatus : SM9fFullNoNewForwardAlgebraStatus
  noNewForwardAlgebraStatus_eq :
    noNewForwardAlgebraStatus = SM9fFullNoNewForwardAlgebraStatus.noNewForwardAlgebraLayer
  noNewCoefficientRecurrenceStatus : SM9fNoNewCoefficientRecurrenceStatus
  noNewCoefficientRecurrenceStatus_eq :
    noNewCoefficientRecurrenceStatus =
      SM9fNoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
  noFreeDeterminantOracleStatus : SM9fNoFreeDeterminantOracleStatus
  noFreeDeterminantOracleStatus_eq :
    noFreeDeterminantOracleStatus =
      SM9fNoFreeDeterminantOracleStatus.noFreeDeterminantOracleInSM9fLayer
  noPolynomialSemiringRuntimeStatus : SM9fNoPolynomialSemiringRuntimeStatus
  noPolynomialSemiringRuntimeStatus_eq :
    noPolynomialSemiringRuntimeStatus =
      SM9fNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noMathlibPolynomialOperationalPathStatus : SM9fNoMathlibPolynomialOperationalPathStatus
  noMathlibPolynomialOperationalPathStatus_eq :
    noMathlibPolynomialOperationalPathStatus =
      SM9fNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noMatrixCharpolyOracleStatus : SM9fNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9fNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noFactorizationStatus : SM9fNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9fNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9fNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9fNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9fNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9fNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9fNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9fNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9fNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9fNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9fNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9fNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9fNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9fNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9fNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9fNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

namespace GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedBoundaryIndex A)]
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
variable {G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H}

def fromForwardSource
    (Q : GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f Cell p A P wp W E K T M S H G)
    (F : GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1 Cell p A P wp W E K T M S H G) :
    GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus Cell p A P wp W E K T M S H G :=
  { sourceSM9fRequirement := Q
    sourceSM9ePlus1 := F
    sourceSM9ePlus1_nextPhase_eq_SM9fFull := F.nextPhaseStatus_eq
    sourceSM9ePlus1_forwardStatus_eq := F.forwardEvaluationStatus_eq
    forwardEvaluationAtSource := Q.determinantEvaluationAtSource
    forwardEvaluationAtSource_eq_SM9dEvaluationAtSource := Q.determinantEvaluationAtSource_eq_SM9d
    forwardEvaluationAtSource_eq_SM9cEvaluationFamilyAtSource :=
      Q.determinantEvaluationAtSource_eq_SM9cFamily
    forwardEvaluationAtSource_eq_SM9cDetPencilAtSource :=
      Q.determinantEvaluationAtSource_eq_SM9cDetPencil
    linearPencilForwardTarget_closed := F.linearPencilForwardTarget_closed
    forwardEvaluationTargetStatement := F.forwardEvaluationTargetStatement
    forwardEvaluationTargetStatement_eq := F.forwardEvaluationTargetStatement_eq
    bridgeStatus :=
      SM9fFullDeterminantForwardBridgeStatus.determinantForwardBridgeClosedFromSM9ePlusSource
    bridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9fFullNextPhaseStatus.discriminantFactorGateAfterForwardBridge
    nextPhaseStatus_eq := by
      rfl
    oldEvalOrientationPatchStatus :=
      SM9fFullOldEvalOrientationPatchStatus.oldEvalOrientationNotUsedAsBridgeInput
    oldEvalOrientationPatchStatus_eq := by
      rfl
    noNewForwardAlgebraStatus := SM9fFullNoNewForwardAlgebraStatus.noNewForwardAlgebraLayer
    noNewForwardAlgebraStatus_eq := by
      rfl
    noNewCoefficientRecurrenceStatus :=
      SM9fNoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
    noNewCoefficientRecurrenceStatus_eq := by
      rfl
    noFreeDeterminantOracleStatus :=
      SM9fNoFreeDeterminantOracleStatus.noFreeDeterminantOracleInSM9fLayer
    noFreeDeterminantOracleStatus_eq := by
      rfl
    noPolynomialSemiringRuntimeStatus :=
      SM9fNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
    noPolynomialSemiringRuntimeStatus_eq := by
      rfl
    noMathlibPolynomialOperationalPathStatus :=
      SM9fNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
    noMathlibPolynomialOperationalPathStatus_eq := by
      rfl
    noMatrixCharpolyOracleStatus := SM9fNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
    noMatrixCharpolyOracleStatus_eq := by
      rfl
    noFactorizationStatus := SM9fNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9fNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9fNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9fNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9fNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9fNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9fNoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9fNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl }

theorem forwardEvaluationAtSource_eq_SM9dEvaluationAtSource_projection
    (B : GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.{u, v}
      Cell p A P wp W E K T M S H G) :
    B.forwardEvaluationAtSource = B.sourceSM9fRequirement.sourceSM9e.sourceSM9d.evaluationAtSource :=
  B.forwardEvaluationAtSource_eq_SM9dEvaluationAtSource

theorem forwardEvaluationAtSource_eq_SM9cDetPencilAtSource_projection
    (B : GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.{u, v}
      Cell p A P wp W E K T M S H G) :
    B.forwardEvaluationAtSource =
      Matrix.det B.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  B.forwardEvaluationAtSource_eq_SM9cDetPencilAtSource

theorem linearPencilForwardTarget_closed_projection
    (B : GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.{u, v}
      Cell p A P wp W E K T M S H G)
    {ι : Type v} [DecidableEq ι]
    (X : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (operationalLinearPencilEntryPolynomialSM9e 1 X i j) z =
      (-(X i j)) +
        Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0) :=
  B.linearPencilForwardTarget_closed X i j z

theorem bridgeClosedFromSM9ePlusSource
    (B : GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.{u, v}
      Cell p A P wp W E K T M S H G) :
    B.bridgeStatus =
      SM9fFullDeterminantForwardBridgeStatus.determinantForwardBridgeClosedFromSM9ePlusSource :=
  B.bridgeStatus_eq

end GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus

def regularGeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9ePlus0Ledger.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  let Q :=
    regularGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
      L.sourceSM9ePlus0Ledger.sourceSM9eLedger
  GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.fromForwardSource Q L.regularForwardSource

def variableGeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9ePlus0Ledger.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  let Q :=
    variableGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
      L.sourceSM9ePlus0Ledger.sourceSM9eLedger
  GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.fromForwardSource Q L.variableForwardSource

structure SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9ePlus1Ledger :
    SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z
  sourceSM9fRequirementLedger :
    SM9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
      b β p regularWeight variableWeight z
  sourceSM9fRequirementLedger_eq_from_SM9ePlus1 :
    sourceSM9fRequirementLedger =
      sm9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
        sourceSM9ePlus1Ledger.sourceSM9ePlus0Ledger.sourceSM9eLedger
  regularBridge :
    GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9ePlus1Ledger.sourceSM9ePlus0Ledger.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableBridge :
    GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9ePlus1Ledger.sourceSM9ePlus0Ledger.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularBridge_eq_from_SM9ePlus1 :
    regularBridge = regularGeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
      sourceSM9ePlus1Ledger
  variableBridge_eq_from_SM9ePlus1 :
    variableBridge = variableGeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus
      sourceSM9ePlus1Ledger
  regularForwardEvaluationAtSource_eq_SM9d :
    regularBridge.forwardEvaluationAtSource =
      regularBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.evaluationAtSource
  variableForwardEvaluationAtSource_eq_SM9d :
    variableBridge.forwardEvaluationAtSource =
      variableBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.evaluationAtSource
  regularForwardEvaluationAtSource_eq_SM9cDetPencil :
    regularBridge.forwardEvaluationAtSource =
      Matrix.det regularBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  variableForwardEvaluationAtSource_eq_SM9cDetPencil :
    variableBridge.forwardEvaluationAtSource =
      Matrix.det variableBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  bridgeStatus : SM9fFullDeterminantForwardBridgeStatus
  bridgeStatus_eq :
    bridgeStatus =
      SM9fFullDeterminantForwardBridgeStatus.determinantForwardBridgeClosedFromSM9ePlusSource
  nextPhaseStatus : SM9fFullNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9fFullNextPhaseStatus.discriminantFactorGateAfterForwardBridge
  oldEvalOrientationPatchStatus : SM9fFullOldEvalOrientationPatchStatus
  oldEvalOrientationPatchStatus_eq :
    oldEvalOrientationPatchStatus =
      SM9fFullOldEvalOrientationPatchStatus.oldEvalOrientationNotUsedAsBridgeInput
  noNewForwardAlgebraStatus : SM9fFullNoNewForwardAlgebraStatus
  noNewForwardAlgebraStatus_eq :
    noNewForwardAlgebraStatus = SM9fFullNoNewForwardAlgebraStatus.noNewForwardAlgebraLayer
  noFactorizationStatus : SM9fNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9fNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9fNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9fNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9fNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9fNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9fNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9fNoCMTargetStatus.noCMTarget

def sm9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z) :
    SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z :=
  let Q := sm9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
    L.sourceSM9ePlus0Ledger.sourceSM9eLedger
  let R := regularGeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus L
  let V := variableGeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus L
  { sourceSM9ePlus1Ledger := L
    sourceSM9fRequirementLedger := Q
    sourceSM9fRequirementLedger_eq_from_SM9ePlus1 := by
      rfl
    regularBridge := R
    variableBridge := V
    regularBridge_eq_from_SM9ePlus1 := by
      rfl
    variableBridge_eq_from_SM9ePlus1 := by
      rfl
    regularForwardEvaluationAtSource_eq_SM9d := R.forwardEvaluationAtSource_eq_SM9dEvaluationAtSource
    variableForwardEvaluationAtSource_eq_SM9d := V.forwardEvaluationAtSource_eq_SM9dEvaluationAtSource
    regularForwardEvaluationAtSource_eq_SM9cDetPencil :=
      R.forwardEvaluationAtSource_eq_SM9cDetPencilAtSource
    variableForwardEvaluationAtSource_eq_SM9cDetPencil :=
      V.forwardEvaluationAtSource_eq_SM9cDetPencilAtSource
    bridgeStatus :=
      SM9fFullDeterminantForwardBridgeStatus.determinantForwardBridgeClosedFromSM9ePlusSource
    bridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9fFullNextPhaseStatus.discriminantFactorGateAfterForwardBridge
    nextPhaseStatus_eq := by
      rfl
    oldEvalOrientationPatchStatus :=
      SM9fFullOldEvalOrientationPatchStatus.oldEvalOrientationNotUsedAsBridgeInput
    oldEvalOrientationPatchStatus_eq := by
      rfl
    noNewForwardAlgebraStatus := SM9fFullNoNewForwardAlgebraStatus.noNewForwardAlgebraLayer
    noNewForwardAlgebraStatus_eq := by
      rfl
    noFactorizationStatus := SM9fNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9fNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9fNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9fNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl }

def sm9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger_from_SM9eLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z :=
  sm9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
    (sm9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger_from_SM9eLedger L)

theorem sm9fFull_regularForwardEvaluationAtSource_eq_SM9d
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.regularBridge.forwardEvaluationAtSource =
      L.regularBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.evaluationAtSource :=
  L.regularForwardEvaluationAtSource_eq_SM9d

theorem sm9fFull_variableForwardEvaluationAtSource_eq_SM9d
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.variableBridge.forwardEvaluationAtSource =
      L.variableBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.evaluationAtSource :=
  L.variableForwardEvaluationAtSource_eq_SM9d

theorem sm9fFull_regularForwardEvaluationAtSource_eq_SM9cDetPencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.regularBridge.forwardEvaluationAtSource =
      Matrix.det L.regularBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  L.regularForwardEvaluationAtSource_eq_SM9cDetPencil

theorem sm9fFull_nextPhase_eq_discriminantFactorGate
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9fFullNextPhaseStatus.discriminantFactorGateAfterForwardBridge :=
  L.nextPhaseStatus_eq

theorem sm9fFull_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9fNoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
