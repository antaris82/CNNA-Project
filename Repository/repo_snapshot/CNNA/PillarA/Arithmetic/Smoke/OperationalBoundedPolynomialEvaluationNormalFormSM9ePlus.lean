import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u v

inductive SM9ePlus0EvaluationNormalFormStatus where
  | operationalBoundedPolynomialEvaluationNormalFormExposed
  deriving DecidableEq, Repr

inductive SM9ePlus0EvaluationOrientationStatus where
  | currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  deriving DecidableEq, Repr

inductive SM9ePlus0ForwardEvaluationStatus where
  | forwardEvaluationSourceRequiredBeforeSM9fFull
  deriving DecidableEq, Repr

inductive SM9ePlus0NextPhaseStatus where
  | sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull
  deriving DecidableEq, Repr

inductive SM9ePlus0NoNewMatrixStatus where
  | noNewMatrix
  deriving DecidableEq, Repr

inductive SM9ePlus0NoNewDeterminantSourceStatus where
  | noNewDeterminantSource
  deriving DecidableEq, Repr

inductive SM9ePlus0NoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9ePlus0NoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9ePlus0NoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9ePlus0NoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9ePlus0NoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9ePlus0NoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9ePlus0NoScalarInvStatus where
  | noScalarInv
  deriving DecidableEq, Repr

inductive SM9ePlus0NoNoncomputableOperationalSourceStatus where
  | noNoncomputableOperationalSource
  deriving DecidableEq, Repr

namespace OperationalBoundedPolynomialSM9e

theorem eval_zero (z : Schur.SpectralParameter) :
    eval (zero 0) z = 0 := by
  rfl

theorem eval_one (z : Schur.SpectralParameter) :
    eval (one 0) z = 1 := by
  rfl

theorem eval_const (c : ExecComplex) (z : Schur.SpectralParameter) :
    eval (const 0 c) z = c := by
  rfl

theorem eval_linear_degreeOne_current
    (c0 c1 : ExecComplex) (z : Schur.SpectralParameter) :
    eval (linear 1 c0 c1) z = c1 + Schur.spectralParameterExec z * c0 := by
  rfl

end OperationalBoundedPolynomialSM9e

theorem operationalLinearPencilEntry_eval_degreeOne_current
    {ι : Type v} [DecidableEq ι]
    (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.eval
        (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
      (if i = j then (1 : ExecComplex) else 0) +
        Schur.spectralParameterExec z * (-(A i j)) := by
  rfl

def operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus0 : Prop :=
  ∀ {ι : Type v} [DecidableEq ι]
    (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
    OperationalBoundedPolynomialSM9e.eval
        (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
      (-(A i j)) +
        Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0)

structure OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 where
  eval_zero :
    ∀ z : Schur.SpectralParameter,
      OperationalBoundedPolynomialSM9e.eval
        (OperationalBoundedPolynomialSM9e.zero 0) z = 0
  eval_one :
    ∀ z : Schur.SpectralParameter,
      OperationalBoundedPolynomialSM9e.eval
        (OperationalBoundedPolynomialSM9e.one 0) z = 1
  eval_const :
    ∀ (c : ExecComplex) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.eval
        (OperationalBoundedPolynomialSM9e.const 0 c) z = c
  eval_linear_degreeOne_current :
    ∀ (c0 c1 : ExecComplex) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.eval
        (OperationalBoundedPolynomialSM9e.linear 1 c0 c1) z =
        c1 + Schur.spectralParameterExec z * c0
  linearPencilEntry_degreeOne_current :
    ∀ {ι : Type v} [DecidableEq ι]
      (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.eval
          (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
        (if i = j then (1 : ExecComplex) else 0) +
          Schur.spectralParameterExec z * (-(A i j))
  spectralPencilEntryTargetStatement : Prop
  spectralPencilEntryTargetStatement_eq :
    spectralPencilEntryTargetStatement =
      operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus0
  normalFormStatus : SM9ePlus0EvaluationNormalFormStatus
  normalFormStatus_eq :
    normalFormStatus =
      SM9ePlus0EvaluationNormalFormStatus.operationalBoundedPolynomialEvaluationNormalFormExposed
  orientationStatus : SM9ePlus0EvaluationOrientationStatus
  orientationStatus_eq :
    orientationStatus =
      SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  forwardEvaluationStatus : SM9ePlus0ForwardEvaluationStatus
  forwardEvaluationStatus_eq :
    forwardEvaluationStatus =
      SM9ePlus0ForwardEvaluationStatus.forwardEvaluationSourceRequiredBeforeSM9fFull
  noNewMatrixStatus : SM9ePlus0NoNewMatrixStatus
  noNewMatrixStatus_eq :
    noNewMatrixStatus = SM9ePlus0NoNewMatrixStatus.noNewMatrix
  noNewDeterminantSourceStatus : SM9ePlus0NoNewDeterminantSourceStatus
  noNewDeterminantSourceStatus_eq :
    noNewDeterminantSourceStatus =
      SM9ePlus0NoNewDeterminantSourceStatus.noNewDeterminantSource
  noFactorizationStatus : SM9ePlus0NoFactorizationStatus
  noFactorizationStatus_eq :
    noFactorizationStatus = SM9ePlus0NoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9ePlus0NoDiscriminantStatus
  noDiscriminantStatus_eq :
    noDiscriminantStatus = SM9ePlus0NoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9ePlus0NoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9ePlus0NoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9ePlus0NoCMTargetStatus
  noCMTargetStatus_eq :
    noCMTargetStatus = SM9ePlus0NoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9ePlus0NoMatrixInvStatus
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM9ePlus0NoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9ePlus0NoFieldSimpStatus
  noFieldSimpStatus_eq :
    noFieldSimpStatus = SM9ePlus0NoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9ePlus0NoScalarInvStatus
  noScalarInvStatus_eq :
    noScalarInvStatus = SM9ePlus0NoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9ePlus0NoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9ePlus0NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

def operationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 :
    OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 where
  eval_zero := OperationalBoundedPolynomialSM9e.eval_zero
  eval_one := OperationalBoundedPolynomialSM9e.eval_one
  eval_const := OperationalBoundedPolynomialSM9e.eval_const
  eval_linear_degreeOne_current :=
    OperationalBoundedPolynomialSM9e.eval_linear_degreeOne_current
  linearPencilEntry_degreeOne_current :=
    operationalLinearPencilEntry_eval_degreeOne_current
  spectralPencilEntryTargetStatement :=
    operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus0
  spectralPencilEntryTargetStatement_eq := by
    rfl
  normalFormStatus :=
    SM9ePlus0EvaluationNormalFormStatus.operationalBoundedPolynomialEvaluationNormalFormExposed
  normalFormStatus_eq := by
    rfl
  orientationStatus :=
    SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  orientationStatus_eq := by
    rfl
  forwardEvaluationStatus :=
    SM9ePlus0ForwardEvaluationStatus.forwardEvaluationSourceRequiredBeforeSM9fFull
  forwardEvaluationStatus_eq := by
    rfl
  noNewMatrixStatus := SM9ePlus0NoNewMatrixStatus.noNewMatrix
  noNewMatrixStatus_eq := by
    rfl
  noNewDeterminantSourceStatus :=
    SM9ePlus0NoNewDeterminantSourceStatus.noNewDeterminantSource
  noNewDeterminantSourceStatus_eq := by
    rfl
  noFactorizationStatus := SM9ePlus0NoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9ePlus0NoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9ePlus0NoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9ePlus0NoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9ePlus0NoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9ePlus0NoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noScalarInvStatus := SM9ePlus0NoScalarInvStatus.noScalarInv
  noScalarInvStatus_eq := by
    rfl
  noNoncomputableOperationalSourceStatus :=
    SM9ePlus0NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noNoncomputableOperationalSourceStatus_eq := by
    rfl

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

structure GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
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
  normalForm : OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
  normalForm_eq :
    normalForm = operationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
  evaluationAtSource_eq_coefficients :
    sourceSM9e.evaluationAtSource =
      sourceSM9e.evaluationFromCoefficients sourceSM9e.sourceSM9d.sourceParameter
  currentLinearEntryOrientation :
    ∀ {ι : Type v} [DecidableEq ι]
      (B : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.eval
          (operationalLinearPencilEntryPolynomialSM9e 1 B i j) z =
        (if i = j then (1 : ExecComplex) else 0) +
          Schur.spectralParameterExec z * (-(B i j))
  spectralPencilEntryTargetStatement : Prop
  spectralPencilEntryTargetStatement_eq :
    spectralPencilEntryTargetStatement =
      operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus0
  normalFormStatus : SM9ePlus0EvaluationNormalFormStatus
  normalFormStatus_eq :
    normalFormStatus =
      SM9ePlus0EvaluationNormalFormStatus.operationalBoundedPolynomialEvaluationNormalFormExposed
  orientationStatus : SM9ePlus0EvaluationOrientationStatus
  orientationStatus_eq :
    orientationStatus =
      SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  forwardEvaluationStatus : SM9ePlus0ForwardEvaluationStatus
  forwardEvaluationStatus_eq :
    forwardEvaluationStatus =
      SM9ePlus0ForwardEvaluationStatus.forwardEvaluationSourceRequiredBeforeSM9fFull
  nextPhaseStatus : SM9ePlus0NextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM9ePlus0NextPhaseStatus.sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull
  noNewMatrixStatus : SM9ePlus0NoNewMatrixStatus
  noNewMatrixStatus_eq :
    noNewMatrixStatus = SM9ePlus0NoNewMatrixStatus.noNewMatrix
  noNewDeterminantSourceStatus : SM9ePlus0NoNewDeterminantSourceStatus
  noNewDeterminantSourceStatus_eq :
    noNewDeterminantSourceStatus =
      SM9ePlus0NoNewDeterminantSourceStatus.noNewDeterminantSource
  noFactorizationStatus : SM9ePlus0NoFactorizationStatus
  noFactorizationStatus_eq :
    noFactorizationStatus = SM9ePlus0NoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9ePlus0NoDiscriminantStatus
  noDiscriminantStatus_eq :
    noDiscriminantStatus = SM9ePlus0NoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9ePlus0NoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9ePlus0NoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9ePlus0NoCMTargetStatus
  noCMTargetStatus_eq :
    noCMTargetStatus = SM9ePlus0NoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9ePlus0NoMatrixInvStatus
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM9ePlus0NoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9ePlus0NoFieldSimpStatus
  noFieldSimpStatus_eq :
    noFieldSimpStatus = SM9ePlus0NoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9ePlus0NoScalarInvStatus
  noScalarInvStatus_eq :
    noScalarInvStatus = SM9ePlus0NoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9ePlus0NoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9ePlus0NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

namespace GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0

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
    GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
      Cell p A P wp W E K T M S H G where
  sourceSM9e := R
  normalForm := operationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
  normalForm_eq := by
    rfl
  evaluationAtSource_eq_coefficients := R.evaluationAtSource_eq_coefficients
  currentLinearEntryOrientation := operationalLinearPencilEntry_eval_degreeOne_current
  spectralPencilEntryTargetStatement :=
    operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus0
  spectralPencilEntryTargetStatement_eq := by
    rfl
  normalFormStatus :=
    SM9ePlus0EvaluationNormalFormStatus.operationalBoundedPolynomialEvaluationNormalFormExposed
  normalFormStatus_eq := by
    rfl
  orientationStatus :=
    SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  orientationStatus_eq := by
    rfl
  forwardEvaluationStatus :=
    SM9ePlus0ForwardEvaluationStatus.forwardEvaluationSourceRequiredBeforeSM9fFull
  forwardEvaluationStatus_eq := by
    rfl
  nextPhaseStatus :=
    SM9ePlus0NextPhaseStatus.sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull
  nextPhaseStatus_eq := by
    rfl
  noNewMatrixStatus := SM9ePlus0NoNewMatrixStatus.noNewMatrix
  noNewMatrixStatus_eq := by
    rfl
  noNewDeterminantSourceStatus :=
    SM9ePlus0NoNewDeterminantSourceStatus.noNewDeterminantSource
  noNewDeterminantSourceStatus_eq := by
    rfl
  noFactorizationStatus := SM9ePlus0NoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9ePlus0NoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9ePlus0NoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9ePlus0NoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9ePlus0NoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9ePlus0NoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noScalarInvStatus := SM9ePlus0NoScalarInvStatus.noScalarInv
  noScalarInvStatus_eq := by
    rfl
  noNoncomputableOperationalSourceStatus :=
    SM9ePlus0NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noNoncomputableOperationalSourceStatus_eq := by
    rfl

theorem current_orientation
    (N : GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0.{u, v}
      Cell p A P wp W E K T M S H G)
    {ι : Type v} [DecidableEq ι]
    (B : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.eval
        (operationalLinearPencilEntryPolynomialSM9e 1 B i j) z =
      (if i = j then (1 : ExecComplex) else 0) +
        Schur.spectralParameterExec z * (-(B i j)) := by
  exact N.currentLinearEntryOrientation (ι := ι) B i j z


theorem nextPhase_eq_forwardEvaluationSource
    (N : GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
      Cell p A P wp W E K T M S H G) :
    N.nextPhaseStatus =
      SM9ePlus0NextPhaseStatus.sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull :=
  N.nextPhaseStatus_eq

end GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0

def regularGeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
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
  GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0.fromSM9e L.regularRecurrence

def variableGeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
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
  GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0.fromSM9e L.variableRecurrence

structure SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9eLedger :
    SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger b β p regularWeight variableWeight z
  regularNormalForm :
    GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
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
  variableNormalForm :
    GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
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
  regularNormalForm_eq_from_SM9e :
    regularNormalForm =
      regularGeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 sourceSM9eLedger
  variableNormalForm_eq_from_SM9e :
    variableNormalForm =
      variableGeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 sourceSM9eLedger
  regularOrientationStatus_eq :
    regularNormalForm.orientationStatus =
      SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  variableOrientationStatus_eq :
    variableNormalForm.orientationStatus =
      SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero
  regularForwardEvaluationStatus_eq :
    regularNormalForm.forwardEvaluationStatus =
      SM9ePlus0ForwardEvaluationStatus.forwardEvaluationSourceRequiredBeforeSM9fFull
  variableForwardEvaluationStatus_eq :
    variableNormalForm.forwardEvaluationStatus =
      SM9ePlus0ForwardEvaluationStatus.forwardEvaluationSourceRequiredBeforeSM9fFull
  regularNextPhaseStatus_eq :
    regularNormalForm.nextPhaseStatus =
      SM9ePlus0NextPhaseStatus.sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull
  variableNextPhaseStatus_eq :
    variableNormalForm.nextPhaseStatus =
      SM9ePlus0NextPhaseStatus.sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull
  noFactorizationStatus : SM9ePlus0NoFactorizationStatus
  noFactorizationStatus_eq :
    noFactorizationStatus = SM9ePlus0NoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9ePlus0NoDiscriminantStatus
  noDiscriminantStatus_eq :
    noDiscriminantStatus = SM9ePlus0NoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9ePlus0NoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9ePlus0NoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9ePlus0NoCMTargetStatus
  noCMTargetStatus_eq :
    noCMTargetStatus = SM9ePlus0NoCMTargetStatus.noCMTarget
  noNewMatrixStatus : SM9ePlus0NoNewMatrixStatus
  noNewMatrixStatus_eq :
    noNewMatrixStatus = SM9ePlus0NoNewMatrixStatus.noNewMatrix
  noNewDeterminantSourceStatus : SM9ePlus0NoNewDeterminantSourceStatus
  noNewDeterminantSourceStatus_eq :
    noNewDeterminantSourceStatus =
      SM9ePlus0NoNewDeterminantSourceStatus.noNewDeterminantSource

def sm9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z :=
  let R := regularGeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 L
  let V := variableGeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 L
  { sourceSM9eLedger := L
    regularNormalForm := R
    variableNormalForm := V
    regularNormalForm_eq_from_SM9e := by
      rfl
    variableNormalForm_eq_from_SM9e := by
      rfl
    regularOrientationStatus_eq := R.orientationStatus_eq
    variableOrientationStatus_eq := V.orientationStatus_eq
    regularForwardEvaluationStatus_eq := R.forwardEvaluationStatus_eq
    variableForwardEvaluationStatus_eq := V.forwardEvaluationStatus_eq
    regularNextPhaseStatus_eq := R.nextPhaseStatus_eq
    variableNextPhaseStatus_eq := V.nextPhaseStatus_eq
    noFactorizationStatus := SM9ePlus0NoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9ePlus0NoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9ePlus0NoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9ePlus0NoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noNewMatrixStatus := SM9ePlus0NoNewMatrixStatus.noNewMatrix
    noNewMatrixStatus_eq := by
      rfl
    noNewDeterminantSourceStatus :=
      SM9ePlus0NoNewDeterminantSourceStatus.noNewDeterminantSource
    noNewDeterminantSourceStatus_eq := by
      rfl }

theorem sm9ePlus0_regularCurrentOrientationStatus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    L.regularNormalForm.orientationStatus =
      SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero :=
  L.regularOrientationStatus_eq

theorem sm9ePlus0_variableCurrentOrientationStatus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    L.variableNormalForm.orientationStatus =
      SM9ePlus0EvaluationOrientationStatus.currentDegreeOneLinearEvalIsCoefficientOnePlusZTimesCoefficientZero :=
  L.variableOrientationStatus_eq

theorem sm9ePlus0_regularNextPhase_eq_SM9ePlus1
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    L.regularNormalForm.nextPhaseStatus =
      SM9ePlus0NextPhaseStatus.sm9ePlus1ForwardEvaluationSourceBeforeSM9fFull :=
  L.regularNextPhaseStatus_eq

theorem sm9ePlus0_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9ePlus0NoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
