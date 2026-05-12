import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM9fDeterminantEvaluationBridgeStatus where
  | determinantEvaluationBridgeClosedBeforeDiscriminantGate
  | determinantEvaluationBridgeRequiresSM9eEvaluationLemma
  deriving DecidableEq, Repr

inductive SM9fNextPhaseStatus where
  | discriminantFactorGateAfterClosedBridge
  | sm9ePlusBeforeDiscriminantGate
  deriving DecidableEq, Repr

inductive SM9fNoNewCoefficientRecurrenceStatus where
  | noNewCoefficientRecurrence
  deriving DecidableEq, Repr

inductive SM9fNoFreeDeterminantOracleStatus where
  | noFreeDeterminantOracleInSM9fLayer
  deriving DecidableEq, Repr

inductive SM9fNoPolynomialSemiringRuntimeStatus where
  | noPolynomialSemiringRuntime
  deriving DecidableEq, Repr

inductive SM9fNoMathlibPolynomialOperationalPathStatus where
  | noMathlibPolynomialOperationalPath
  deriving DecidableEq, Repr

inductive SM9fNoMatrixCharpolyOracleStatus where
  | noMatrixCharpolyOracle
  deriving DecidableEq, Repr

inductive SM9fNoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9fNoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9fNoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9fNoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9fNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9fNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9fNoScalarInvStatus where
  | noScalarInv
  deriving DecidableEq, Repr

inductive SM9fNoNoncomputableOperationalSourceStatus where
  | noNoncomputableOperationalSource
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

structure GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
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
  sourceSM9e : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
    Cell p A P wp W E K T M S H G
  coefficientEvaluationAtSource : ExecComplex
  coefficientEvaluationAtSource_eq_SM9e :
    coefficientEvaluationAtSource = sourceSM9e.evaluationAtSource
  determinantEvaluationAtSource : ExecComplex
  determinantEvaluationAtSource_eq_SM9d :
    determinantEvaluationAtSource = sourceSM9e.sourceSM9d.evaluationAtSource
  determinantEvaluationAtSource_eq_SM9cFamily :
    determinantEvaluationAtSource =
      sourceSM9e.sourceSM9d.sourceSM9c.evaluationFamily sourceSM9e.sourceSM9d.sourceParameter
  determinantEvaluationAtSource_eq_SM9cDetPencil :
    determinantEvaluationAtSource =
      Matrix.det sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  bridgeTargetStatement : Prop
  bridgeTargetStatement_eq :
    bridgeTargetStatement =
      (sourceSM9e.evaluationAtSource = sourceSM9e.sourceSM9d.evaluationAtSource)
  bridgeStatus : SM9fDeterminantEvaluationBridgeStatus
  bridgeStatus_eq :
    bridgeStatus =
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeRequiresSM9eEvaluationLemma
  nextPhaseStatus : SM9fNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9fNextPhaseStatus.sm9ePlusBeforeDiscriminantGate
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

namespace GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f

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

def fromSM9e
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f Cell p A P wp W E K T M S H G :=
  let hFamily := congrArg (fun f => f R.sourceSM9d.sourceParameter) R.sourceSM9d.evaluationFamily_eq_SM9c
  { sourceSM9e := R
    coefficientEvaluationAtSource := R.evaluationAtSource
    coefficientEvaluationAtSource_eq_SM9e := by
      rfl
    determinantEvaluationAtSource := R.sourceSM9d.evaluationAtSource
    determinantEvaluationAtSource_eq_SM9d := by
      rfl
    determinantEvaluationAtSource_eq_SM9cFamily := by
      exact R.sourceSM9d.evaluationAtSource_eq_family.trans hFamily
    determinantEvaluationAtSource_eq_SM9cDetPencil := by
      exact R.sourceSM9d.evaluationAtSource_eq_det_pencil
    bridgeTargetStatement := R.evaluationAtSource = R.sourceSM9d.evaluationAtSource
    bridgeTargetStatement_eq := by
      rfl
    bridgeStatus :=
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeRequiresSM9eEvaluationLemma
    bridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9fNextPhaseStatus.sm9ePlusBeforeDiscriminantGate
    nextPhaseStatus_eq := by
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

theorem bridgeTarget_eq_source_target
    (Q : GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f Cell p A P wp W E K T M S H G) :
    Q.bridgeTargetStatement =
      (Q.sourceSM9e.evaluationAtSource = Q.sourceSM9e.sourceSM9d.evaluationAtSource) :=
  Q.bridgeTargetStatement_eq

theorem determinantEvaluationAtSource_eq_SM9cDetPencil_projection
    (Q : GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f Cell p A P wp W E K T M S H G) :
    Q.determinantEvaluationAtSource =
      Matrix.det Q.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  Q.determinantEvaluationAtSource_eq_SM9cDetPencil

end GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f

structure GeneratedOperationalDeterminantEvaluationBridgeFromSM9e
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
  sourceSM9e : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
    Cell p A P wp W E K T M S H G
  evaluationFromCoefficients_eq_SM9dEvaluationAtSource :
    sourceSM9e.evaluationAtSource = sourceSM9e.sourceSM9d.evaluationAtSource
  evaluationFromCoefficients_eq_SM9cEvaluationFamilyAtSource :
    sourceSM9e.evaluationAtSource =
      sourceSM9e.sourceSM9d.sourceSM9c.evaluationFamily sourceSM9e.sourceSM9d.sourceParameter
  evaluationFromCoefficients_eq_SM9cDetPencilAtSource :
    sourceSM9e.evaluationAtSource =
      Matrix.det sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  bridgeStatus : SM9fDeterminantEvaluationBridgeStatus
  bridgeStatus_eq :
    bridgeStatus =
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeClosedBeforeDiscriminantGate
  nextPhaseStatus : SM9fNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9fNextPhaseStatus.discriminantFactorGateAfterClosedBridge
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

namespace GeneratedOperationalDeterminantEvaluationBridgeFromSM9e

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

def fromSM9eWithSourceBridge
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G)
    (hBridge : R.evaluationAtSource = R.sourceSM9d.evaluationAtSource) :
    GeneratedOperationalDeterminantEvaluationBridgeFromSM9e Cell p A P wp W E K T M S H G :=
  let hFamily := congrArg (fun f => f R.sourceSM9d.sourceParameter) R.sourceSM9d.evaluationFamily_eq_SM9c
  { sourceSM9e := R
    evaluationFromCoefficients_eq_SM9dEvaluationAtSource := hBridge
    evaluationFromCoefficients_eq_SM9cEvaluationFamilyAtSource := by
      exact hBridge.trans (R.sourceSM9d.evaluationAtSource_eq_family.trans hFamily)
    evaluationFromCoefficients_eq_SM9cDetPencilAtSource := by
      exact hBridge.trans R.sourceSM9d.evaluationAtSource_eq_det_pencil
    bridgeStatus :=
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeClosedBeforeDiscriminantGate
    bridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9fNextPhaseStatus.discriminantFactorGateAfterClosedBridge
    nextPhaseStatus_eq := by
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

theorem evaluationFromCoefficients_eq_SM9cDetPencilAtSource_projection
    (B : GeneratedOperationalDeterminantEvaluationBridgeFromSM9e Cell p A P wp W E K T M S H G) :
    B.sourceSM9e.evaluationAtSource =
      Matrix.det B.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  B.evaluationFromCoefficients_eq_SM9cDetPencilAtSource

theorem bridgeClosedBeforeDiscriminantGate
    (B : GeneratedOperationalDeterminantEvaluationBridgeFromSM9e Cell p A P wp W E K T M S H G) :
    B.bridgeStatus =
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeClosedBeforeDiscriminantGate :=
  B.bridgeStatus_eq

end GeneratedOperationalDeterminantEvaluationBridgeFromSM9e

def regularGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f.fromSM9e L.regularRecurrence

def variableGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f.fromSM9e L.variableRecurrence

def regularGeneratedOperationalDeterminantEvaluationBridgeFromSM9e
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z)
    (hBridge : L.regularRecurrence.evaluationAtSource =
      L.regularRecurrence.sourceSM9d.evaluationAtSource) :
    GeneratedOperationalDeterminantEvaluationBridgeFromSM9e
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedOperationalDeterminantEvaluationBridgeFromSM9e.fromSM9eWithSourceBridge
    L.regularRecurrence hBridge

def variableGeneratedOperationalDeterminantEvaluationBridgeFromSM9e
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z)
    (hBridge : L.variableRecurrence.evaluationAtSource =
      L.variableRecurrence.sourceSM9d.evaluationAtSource) :
    GeneratedOperationalDeterminantEvaluationBridgeFromSM9e
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedOperationalDeterminantEvaluationBridgeFromSM9e.fromSM9eWithSourceBridge
    L.variableRecurrence hBridge

structure SM9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9eLedger :
    SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger b β p regularWeight variableWeight z
  regularRequirement :
    GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableRequirement :
    GeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularRequirement_eq_from_SM9e :
    regularRequirement = regularGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f sourceSM9eLedger
  variableRequirement_eq_from_SM9e :
    variableRequirement = variableGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f sourceSM9eLedger
  regularTargetStatement_eq :
    regularRequirement.bridgeTargetStatement =
      (regularRequirement.sourceSM9e.evaluationAtSource =
        regularRequirement.sourceSM9e.sourceSM9d.evaluationAtSource)
  variableTargetStatement_eq :
    variableRequirement.bridgeTargetStatement =
      (variableRequirement.sourceSM9e.evaluationAtSource =
        variableRequirement.sourceSM9e.sourceSM9d.evaluationAtSource)
  bridgeStatus : SM9fDeterminantEvaluationBridgeStatus
  bridgeStatus_eq :
    bridgeStatus =
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeRequiresSM9eEvaluationLemma
  nextPhaseStatus : SM9fNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9fNextPhaseStatus.sm9ePlusBeforeDiscriminantGate
  noFactorizationStatus : SM9fNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9fNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9fNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9fNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9fNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9fNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9fNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9fNoCMTargetStatus.noCMTarget

def sm9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
      b β p regularWeight variableWeight z :=
  let R := regularGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f L
  let V := variableGeneratedOperationalDeterminantEvaluationBridgeRequirementSM9f L
  { sourceSM9eLedger := L
    regularRequirement := R
    variableRequirement := V
    regularRequirement_eq_from_SM9e := by
      rfl
    variableRequirement_eq_from_SM9e := by
      rfl
    regularTargetStatement_eq := R.bridgeTargetStatement_eq
    variableTargetStatement_eq := V.bridgeTargetStatement_eq
    bridgeStatus :=
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeRequiresSM9eEvaluationLemma
    bridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9fNextPhaseStatus.sm9ePlusBeforeDiscriminantGate
    nextPhaseStatus_eq := by
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

structure SM9fGeneratedOperationalDeterminantEvaluationBridgeLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9eLedger :
    SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger b β p regularWeight variableWeight z
  regularBridge :
    GeneratedOperationalDeterminantEvaluationBridgeFromSM9e
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableBridge :
    GeneratedOperationalDeterminantEvaluationBridgeFromSM9e
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularBridge_source_eq_SM9e :
    regularBridge.sourceSM9e = sourceSM9eLedger.regularRecurrence
  variableBridge_source_eq_SM9e :
    variableBridge.sourceSM9e = sourceSM9eLedger.variableRecurrence
  regularEvaluationFromCoefficients_eq_SM9cDetPencilAtSource :
    regularBridge.sourceSM9e.evaluationAtSource =
      Matrix.det regularBridge.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  variableEvaluationFromCoefficients_eq_SM9cDetPencilAtSource :
    variableBridge.sourceSM9e.evaluationAtSource =
      Matrix.det variableBridge.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  bridgeStatus : SM9fDeterminantEvaluationBridgeStatus
  bridgeStatus_eq :
    bridgeStatus =
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeClosedBeforeDiscriminantGate
  nextPhaseStatus : SM9fNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9fNextPhaseStatus.discriminantFactorGateAfterClosedBridge
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

def sm9fGeneratedOperationalDeterminantEvaluationBridgeLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z)
    (hRegular : L.regularRecurrence.evaluationAtSource =
      L.regularRecurrence.sourceSM9d.evaluationAtSource)
    (hVariable : L.variableRecurrence.evaluationAtSource =
      L.variableRecurrence.sourceSM9d.evaluationAtSource) :
    SM9fGeneratedOperationalDeterminantEvaluationBridgeLedger b β p regularWeight variableWeight z :=
  let R := regularGeneratedOperationalDeterminantEvaluationBridgeFromSM9e L hRegular
  let V := variableGeneratedOperationalDeterminantEvaluationBridgeFromSM9e L hVariable
  { sourceSM9eLedger := L
    regularBridge := R
    variableBridge := V
    regularBridge_source_eq_SM9e := by
      rfl
    variableBridge_source_eq_SM9e := by
      rfl
    regularEvaluationFromCoefficients_eq_SM9cDetPencilAtSource :=
      R.evaluationFromCoefficients_eq_SM9cDetPencilAtSource
    variableEvaluationFromCoefficients_eq_SM9cDetPencilAtSource :=
      V.evaluationFromCoefficients_eq_SM9cDetPencilAtSource
    bridgeStatus :=
      SM9fDeterminantEvaluationBridgeStatus.determinantEvaluationBridgeClosedBeforeDiscriminantGate
    bridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9fNextPhaseStatus.discriminantFactorGateAfterClosedBridge
    nextPhaseStatus_eq := by
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

theorem sm9f_requirement_regularTargetStatement_eq
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
      b β p regularWeight variableWeight z) :
    L.regularRequirement.bridgeTargetStatement =
      (L.regularRequirement.sourceSM9e.evaluationAtSource =
        L.regularRequirement.sourceSM9e.sourceSM9d.evaluationAtSource) :=
  L.regularTargetStatement_eq

theorem sm9f_requirement_variableTargetStatement_eq
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fGeneratedOperationalDeterminantEvaluationBridgeRequirementLedger
      b β p regularWeight variableWeight z) :
    L.variableRequirement.bridgeTargetStatement =
      (L.variableRequirement.sourceSM9e.evaluationAtSource =
        L.variableRequirement.sourceSM9e.sourceSM9d.evaluationAtSource) :=
  L.variableTargetStatement_eq

theorem sm9f_regularEvaluationFromCoefficients_eq_SM9cDetPencilAtSource
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fGeneratedOperationalDeterminantEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.regularBridge.sourceSM9e.evaluationAtSource =
      Matrix.det L.regularBridge.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  L.regularEvaluationFromCoefficients_eq_SM9cDetPencilAtSource

theorem sm9f_variableEvaluationFromCoefficients_eq_SM9cDetPencilAtSource
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fGeneratedOperationalDeterminantEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.variableBridge.sourceSM9e.evaluationAtSource =
      Matrix.det L.variableBridge.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  L.variableEvaluationFromCoefficients_eq_SM9cDetPencilAtSource

theorem sm9f_noFactorization
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fGeneratedOperationalDeterminantEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.noFactorizationStatus = SM9fNoFactorizationStatus.noFactorization :=
  L.noFactorizationStatus_eq

theorem sm9f_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fGeneratedOperationalDeterminantEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9fNoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
