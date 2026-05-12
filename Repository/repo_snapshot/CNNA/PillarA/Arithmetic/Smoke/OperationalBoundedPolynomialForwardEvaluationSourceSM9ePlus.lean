import CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u v

inductive SM9ePlus1ForwardEvaluationStatus where
  | forwardEvaluationSourceFromCoefficientAtClosed
  deriving DecidableEq, Repr

inductive SM9ePlus1SM9fFullReleaseStatus where
  | sm9fFullReleasedOnlyAfterForwardSource
  deriving DecidableEq, Repr

inductive SM9ePlus1NextPhaseStatus where
  | sm9fFullDeterminantEvaluationBridgeFromForwardSource
  deriving DecidableEq, Repr

inductive SM9ePlus1NoNewCoefficientRecurrenceStatus where
  | noNewCoefficientRecurrence
  deriving DecidableEq, Repr

inductive SM9ePlus1NoNewMatrixStatus where
  | noNewMatrix
  deriving DecidableEq, Repr

inductive SM9ePlus1NoNewDeterminantSourceStatus where
  | noNewDeterminantSource
  deriving DecidableEq, Repr

inductive SM9ePlus1NoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9ePlus1NoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9ePlus1NoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9ePlus1NoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9ePlus1NoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9ePlus1NoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9ePlus1NoScalarInvStatus where
  | noScalarInv
  deriving DecidableEq, Repr

inductive SM9ePlus1NoNoncomputableOperationalSourceStatus where
  | noNoncomputableOperationalSource
  deriving DecidableEq, Repr

namespace OperationalBoundedPolynomialSM9e

def forwardEvalDegreeOne
    (P : OperationalBoundedPolynomialSM9e 1) (z : Schur.SpectralParameter) : ExecComplex :=
  coefficientAt P 0 + Schur.spectralParameterExec z * coefficientAt P 1

theorem forwardEvalDegreeOne_eq_coefficientAt
    (P : OperationalBoundedPolynomialSM9e 1) (z : Schur.SpectralParameter) :
    forwardEvalDegreeOne P z =
      coefficientAt P 0 + Schur.spectralParameterExec z * coefficientAt P 1 := by
  rfl

theorem forwardEval_zero (z : Schur.SpectralParameter) :
    forwardEvalDegreeOne (zero 1) z = 0 := by
  apply ExecComplex.ext
  · change 0 + (z * 0 - 0 * 0) = 0
    ring
  · change 0 + (z * 0 + 0 * 0) = 0
    ring

theorem forwardEval_one (z : Schur.SpectralParameter) :
    forwardEvalDegreeOne (one 1) z = 1 := by
  apply ExecComplex.ext
  · change 1 + (z * 0 - 0 * 0) = 1
    ring
  · change 0 + (z * 0 + 0 * 0) = 0
    ring

theorem forwardEval_const (c : ExecComplex) (z : Schur.SpectralParameter) :
    forwardEvalDegreeOne (const 1 c) z = c := by
  apply ExecComplex.ext
  · change c.re + (z * 0 - 0 * 0) = c.re
    ring
  · change c.im + (z * 0 + 0 * 0) = c.im
    ring

theorem forwardEval_linear_degreeOne
    (c0 c1 : ExecComplex) (z : Schur.SpectralParameter) :
    forwardEvalDegreeOne (linear 1 c0 c1) z =
      c0 + Schur.spectralParameterExec z * c1 := by
  rfl

end OperationalBoundedPolynomialSM9e

def operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus1 : Prop :=
  ∀ {ι : Type v} [DecidableEq ι]
    (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
      (-(A i j)) +
        Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0)

theorem operationalLinearPencilEntry_forwardEval_degreeOne
    {ι : Type v} [DecidableEq ι]
    (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
      (-(A i j)) +
        Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0) := by
  rfl

structure OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1 where
  forwardEvalDegreeOne_eq_coefficientAt :
    ∀ (P : OperationalBoundedPolynomialSM9e 1) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne P z =
        OperationalBoundedPolynomialSM9e.coefficientAt P 0 +
          Schur.spectralParameterExec z * OperationalBoundedPolynomialSM9e.coefficientAt P 1
  forwardEval_zero :
    ∀ z : Schur.SpectralParameter,
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (OperationalBoundedPolynomialSM9e.zero 1) z = 0
  forwardEval_one :
    ∀ z : Schur.SpectralParameter,
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (OperationalBoundedPolynomialSM9e.one 1) z = 1
  forwardEval_const :
    ∀ (c : ExecComplex) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (OperationalBoundedPolynomialSM9e.const 1 c) z = c
  forwardEval_linear_degreeOne :
    ∀ (c0 c1 : ExecComplex) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (OperationalBoundedPolynomialSM9e.linear 1 c0 c1) z =
        c0 + Schur.spectralParameterExec z * c1
  linearPencilForwardTarget_closed :
    ∀ {ι : Type v} [DecidableEq ι]
      (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
          (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
        (-(A i j)) +
          Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0)
  forwardEvaluationTargetStatement : Prop
  forwardEvaluationTargetStatement_eq :
    forwardEvaluationTargetStatement =
      operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus1
  forwardEvaluationStatus : SM9ePlus1ForwardEvaluationStatus
  forwardEvaluationStatus_eq :
    forwardEvaluationStatus =
      SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  releaseStatus : SM9ePlus1SM9fFullReleaseStatus
  releaseStatus_eq :
    releaseStatus =
      SM9ePlus1SM9fFullReleaseStatus.sm9fFullReleasedOnlyAfterForwardSource
  nextPhaseStatus : SM9ePlus1NextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  noNewCoefficientRecurrenceStatus : SM9ePlus1NoNewCoefficientRecurrenceStatus
  noNewCoefficientRecurrenceStatus_eq :
    noNewCoefficientRecurrenceStatus =
      SM9ePlus1NoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
  noNewMatrixStatus : SM9ePlus1NoNewMatrixStatus
  noNewMatrixStatus_eq :
    noNewMatrixStatus = SM9ePlus1NoNewMatrixStatus.noNewMatrix
  noNewDeterminantSourceStatus : SM9ePlus1NoNewDeterminantSourceStatus
  noNewDeterminantSourceStatus_eq :
    noNewDeterminantSourceStatus =
      SM9ePlus1NoNewDeterminantSourceStatus.noNewDeterminantSource
  noFactorizationStatus : SM9ePlus1NoFactorizationStatus
  noFactorizationStatus_eq :
    noFactorizationStatus = SM9ePlus1NoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9ePlus1NoDiscriminantStatus
  noDiscriminantStatus_eq :
    noDiscriminantStatus = SM9ePlus1NoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9ePlus1NoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9ePlus1NoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9ePlus1NoCMTargetStatus
  noCMTargetStatus_eq :
    noCMTargetStatus = SM9ePlus1NoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9ePlus1NoMatrixInvStatus
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM9ePlus1NoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9ePlus1NoFieldSimpStatus
  noFieldSimpStatus_eq :
    noFieldSimpStatus = SM9ePlus1NoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9ePlus1NoScalarInvStatus
  noScalarInvStatus_eq :
    noScalarInvStatus = SM9ePlus1NoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9ePlus1NoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9ePlus1NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

def operationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1 :
    OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1 where
  forwardEvalDegreeOne_eq_coefficientAt :=
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne_eq_coefficientAt
  forwardEval_zero := OperationalBoundedPolynomialSM9e.forwardEval_zero
  forwardEval_one := OperationalBoundedPolynomialSM9e.forwardEval_one
  forwardEval_const := OperationalBoundedPolynomialSM9e.forwardEval_const
  forwardEval_linear_degreeOne :=
    OperationalBoundedPolynomialSM9e.forwardEval_linear_degreeOne
  linearPencilForwardTarget_closed :=
    operationalLinearPencilEntry_forwardEval_degreeOne
  forwardEvaluationTargetStatement :=
    operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus1
  forwardEvaluationTargetStatement_eq := by
    rfl
  forwardEvaluationStatus :=
    SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  forwardEvaluationStatus_eq := by
    rfl
  releaseStatus :=
    SM9ePlus1SM9fFullReleaseStatus.sm9fFullReleasedOnlyAfterForwardSource
  releaseStatus_eq := by
    rfl
  nextPhaseStatus :=
    SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  nextPhaseStatus_eq := by
    rfl
  noNewCoefficientRecurrenceStatus :=
    SM9ePlus1NoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
  noNewCoefficientRecurrenceStatus_eq := by
    rfl
  noNewMatrixStatus := SM9ePlus1NoNewMatrixStatus.noNewMatrix
  noNewMatrixStatus_eq := by
    rfl
  noNewDeterminantSourceStatus :=
    SM9ePlus1NoNewDeterminantSourceStatus.noNewDeterminantSource
  noNewDeterminantSourceStatus_eq := by
    rfl
  noFactorizationStatus := SM9ePlus1NoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9ePlus1NoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9ePlus1NoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9ePlus1NoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9ePlus1NoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9ePlus1NoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noScalarInvStatus := SM9ePlus1NoScalarInvStatus.noScalarInv
  noScalarInvStatus_eq := by
    rfl
  noNoncomputableOperationalSourceStatus :=
    SM9ePlus1NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
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

structure GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
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
  sourceSM9ePlus0 : GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
    Cell p A P wp W E K T M S H G
  sourceSM9ePlus0_normalForm_eq :
    sourceSM9ePlus0.normalForm =
      operationalBoundedPolynomialEvaluationNormalFormSM9ePlus0
  forwardSource : OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
  forwardSource_eq :
    forwardSource = operationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
  forwardEvaluationSource_eq_coefficientAt :
    ∀ (P : OperationalBoundedPolynomialSM9e 1) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne P z =
        OperationalBoundedPolynomialSM9e.coefficientAt P 0 +
          Schur.spectralParameterExec z * OperationalBoundedPolynomialSM9e.coefficientAt P 1
  linearPencilForwardTarget_closed :
    ∀ {ι : Type v} [DecidableEq ι]
      (A : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter),
      OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
          (operationalLinearPencilEntryPolynomialSM9e 1 A i j) z =
        (-(A i j)) +
          Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0)
  forwardEvaluationTargetStatement : Prop
  forwardEvaluationTargetStatement_eq :
    forwardEvaluationTargetStatement =
      operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus1
  forwardEvaluationStatus : SM9ePlus1ForwardEvaluationStatus
  forwardEvaluationStatus_eq :
    forwardEvaluationStatus =
      SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  releaseStatus : SM9ePlus1SM9fFullReleaseStatus
  releaseStatus_eq :
    releaseStatus =
      SM9ePlus1SM9fFullReleaseStatus.sm9fFullReleasedOnlyAfterForwardSource
  nextPhaseStatus : SM9ePlus1NextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  noNewCoefficientRecurrenceStatus : SM9ePlus1NoNewCoefficientRecurrenceStatus
  noNewCoefficientRecurrenceStatus_eq :
    noNewCoefficientRecurrenceStatus =
      SM9ePlus1NoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
  noNewMatrixStatus : SM9ePlus1NoNewMatrixStatus
  noNewMatrixStatus_eq :
    noNewMatrixStatus = SM9ePlus1NoNewMatrixStatus.noNewMatrix
  noNewDeterminantSourceStatus : SM9ePlus1NoNewDeterminantSourceStatus
  noNewDeterminantSourceStatus_eq :
    noNewDeterminantSourceStatus =
      SM9ePlus1NoNewDeterminantSourceStatus.noNewDeterminantSource
  noFactorizationStatus : SM9ePlus1NoFactorizationStatus
  noFactorizationStatus_eq :
    noFactorizationStatus = SM9ePlus1NoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9ePlus1NoDiscriminantStatus
  noDiscriminantStatus_eq :
    noDiscriminantStatus = SM9ePlus1NoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9ePlus1NoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9ePlus1NoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9ePlus1NoCMTargetStatus
  noCMTargetStatus_eq :
    noCMTargetStatus = SM9ePlus1NoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9ePlus1NoMatrixInvStatus
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM9ePlus1NoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9ePlus1NoFieldSimpStatus
  noFieldSimpStatus_eq :
    noFieldSimpStatus = SM9ePlus1NoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9ePlus1NoScalarInvStatus
  noScalarInvStatus_eq :
    noScalarInvStatus = SM9ePlus1NoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9ePlus1NoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9ePlus1NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

namespace GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1

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

def fromSM9ePlus0
    (N : GeneratedOperationalBoundedPolynomialEvaluationNormalFormSM9ePlus0 Cell p A P wp W E K T M S H G) :
    GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
      Cell p A P wp W E K T M S H G where
  sourceSM9ePlus0 := N
  sourceSM9ePlus0_normalForm_eq := N.normalForm_eq
  forwardSource := operationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
  forwardSource_eq := by
    rfl
  forwardEvaluationSource_eq_coefficientAt :=
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne_eq_coefficientAt
  linearPencilForwardTarget_closed :=
    operationalLinearPencilEntry_forwardEval_degreeOne
  forwardEvaluationTargetStatement :=
    operationalLinearPencilEntryForwardEvaluationTargetSM9ePlus1
  forwardEvaluationTargetStatement_eq := by
    rfl
  forwardEvaluationStatus :=
    SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  forwardEvaluationStatus_eq := by
    rfl
  releaseStatus :=
    SM9ePlus1SM9fFullReleaseStatus.sm9fFullReleasedOnlyAfterForwardSource
  releaseStatus_eq := by
    rfl
  nextPhaseStatus :=
    SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  nextPhaseStatus_eq := by
    rfl
  noNewCoefficientRecurrenceStatus :=
    SM9ePlus1NoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
  noNewCoefficientRecurrenceStatus_eq := by
    rfl
  noNewMatrixStatus := SM9ePlus1NoNewMatrixStatus.noNewMatrix
  noNewMatrixStatus_eq := by
    rfl
  noNewDeterminantSourceStatus :=
    SM9ePlus1NoNewDeterminantSourceStatus.noNewDeterminantSource
  noNewDeterminantSourceStatus_eq := by
    rfl
  noFactorizationStatus := SM9ePlus1NoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9ePlus1NoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9ePlus1NoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9ePlus1NoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9ePlus1NoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9ePlus1NoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noScalarInvStatus := SM9ePlus1NoScalarInvStatus.noScalarInv
  noScalarInvStatus_eq := by
    rfl
  noNoncomputableOperationalSourceStatus :=
    SM9ePlus1NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noNoncomputableOperationalSourceStatus_eq := by
    rfl

theorem forwardEvaluationTarget_closed_projection
    (F : GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1.{u, v}
      Cell p A P wp W E K T M S H G)
    {ι : Type v} [DecidableEq ι]
    (B : Matrix ι ι ExecComplex) (i j : ι) (z : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (operationalLinearPencilEntryPolynomialSM9e 1 B i j) z =
      (-(B i j)) +
        Schur.spectralParameterExec z * (if i = j then (1 : ExecComplex) else 0) := by
  exact F.linearPencilForwardTarget_closed B i j z

theorem nextPhase_eq_SM9fFull
    (F : GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
      Cell p A P wp W E K T M S H G) :
    F.nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource :=
  F.nextPhaseStatus_eq

end GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1

def regularGeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1.fromSM9ePlus0 L.regularNormalForm

def variableGeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1.fromSM9ePlus0 L.variableNormalForm

structure SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9ePlus0Ledger :
    SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z
  regularForwardSource :
    GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9ePlus0Ledger.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableForwardSource :
    GeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9ePlus0Ledger.sourceSM9eLedger.sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularForwardSource_eq_from_SM9ePlus0 :
    regularForwardSource =
      regularGeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
        sourceSM9ePlus0Ledger
  variableForwardSource_eq_from_SM9ePlus0 :
    variableForwardSource =
      variableGeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1
        sourceSM9ePlus0Ledger
  regularForwardEvaluationStatus_eq :
    regularForwardSource.forwardEvaluationStatus =
      SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  variableForwardEvaluationStatus_eq :
    variableForwardSource.forwardEvaluationStatus =
      SM9ePlus1ForwardEvaluationStatus.forwardEvaluationSourceFromCoefficientAtClosed
  regularNextPhaseStatus_eq :
    regularForwardSource.nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  variableNextPhaseStatus_eq :
    variableForwardSource.nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource
  noNewCoefficientRecurrenceStatus : SM9ePlus1NoNewCoefficientRecurrenceStatus
  noNewCoefficientRecurrenceStatus_eq :
    noNewCoefficientRecurrenceStatus =
      SM9ePlus1NoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
  noNewMatrixStatus : SM9ePlus1NoNewMatrixStatus
  noNewMatrixStatus_eq :
    noNewMatrixStatus = SM9ePlus1NoNewMatrixStatus.noNewMatrix
  noNewDeterminantSourceStatus : SM9ePlus1NoNewDeterminantSourceStatus
  noNewDeterminantSourceStatus_eq :
    noNewDeterminantSourceStatus =
      SM9ePlus1NoNewDeterminantSourceStatus.noNewDeterminantSource
  noFactorizationStatus : SM9ePlus1NoFactorizationStatus
  noFactorizationStatus_eq :
    noFactorizationStatus = SM9ePlus1NoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9ePlus1NoDiscriminantStatus
  noDiscriminantStatus_eq :
    noDiscriminantStatus = SM9ePlus1NoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9ePlus1NoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9ePlus1NoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9ePlus1NoCMTargetStatus
  noCMTargetStatus_eq :
    noCMTargetStatus = SM9ePlus1NoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9ePlus1NoMatrixInvStatus
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM9ePlus1NoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9ePlus1NoFieldSimpStatus
  noFieldSimpStatus_eq :
    noFieldSimpStatus = SM9ePlus1NoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9ePlus1NoScalarInvStatus
  noScalarInvStatus_eq :
    noScalarInvStatus = SM9ePlus1NoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9ePlus1NoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9ePlus1NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

def sm9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger
      b β p regularWeight variableWeight z) :
    SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z :=
  let R := regularGeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1 L
  let V := variableGeneratedOperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus1 L
  { sourceSM9ePlus0Ledger := L
    regularForwardSource := R
    variableForwardSource := V
    regularForwardSource_eq_from_SM9ePlus0 := by
      rfl
    variableForwardSource_eq_from_SM9ePlus0 := by
      rfl
    regularForwardEvaluationStatus_eq := R.forwardEvaluationStatus_eq
    variableForwardEvaluationStatus_eq := V.forwardEvaluationStatus_eq
    regularNextPhaseStatus_eq := R.nextPhaseStatus_eq
    variableNextPhaseStatus_eq := V.nextPhaseStatus_eq
    noNewCoefficientRecurrenceStatus :=
      SM9ePlus1NoNewCoefficientRecurrenceStatus.noNewCoefficientRecurrence
    noNewCoefficientRecurrenceStatus_eq := by
      rfl
    noNewMatrixStatus := SM9ePlus1NoNewMatrixStatus.noNewMatrix
    noNewMatrixStatus_eq := by
      rfl
    noNewDeterminantSourceStatus :=
      SM9ePlus1NoNewDeterminantSourceStatus.noNewDeterminantSource
    noNewDeterminantSourceStatus_eq := by
      rfl
    noFactorizationStatus := SM9ePlus1NoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9ePlus1NoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9ePlus1NoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9ePlus1NoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9ePlus1NoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9ePlus1NoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9ePlus1NoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9ePlus1NoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl }

def sm9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger_from_SM9eLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z :=
  sm9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
    (sm9ePlus0GeneratedOperationalBoundedPolynomialEvaluationNormalFormLedger L)

theorem sm9ePlus1_regularForwardEvaluationTarget_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (_ : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z)
    {ι : Type v} [DecidableEq ι]
    (B : Matrix ι ι ExecComplex) (i j : ι) (w : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (operationalLinearPencilEntryPolynomialSM9e 1 B i j) w =
      (-(B i j)) +
        Schur.spectralParameterExec w * (if i = j then (1 : ExecComplex) else 0) := by
  exact operationalLinearPencilEntry_forwardEval_degreeOne B i j w

theorem sm9ePlus1_variableForwardEvaluationTarget_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (_ : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z)
    {ι : Type v} [DecidableEq ι]
    (B : Matrix ι ι ExecComplex) (i j : ι) (w : Schur.SpectralParameter) :
    OperationalBoundedPolynomialSM9e.forwardEvalDegreeOne
        (operationalLinearPencilEntryPolynomialSM9e 1 B i j) w =
      (-(B i j)) +
        Schur.spectralParameterExec w * (if i = j then (1 : ExecComplex) else 0) := by
  exact operationalLinearPencilEntry_forwardEval_degreeOne B i j w

theorem sm9ePlus1_regularNextPhase_eq_SM9fFull
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z) :
    L.regularForwardSource.nextPhaseStatus =
      SM9ePlus1NextPhaseStatus.sm9fFullDeterminantEvaluationBridgeFromForwardSource :=
  L.regularNextPhaseStatus_eq

theorem sm9ePlus1_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9ePlus1GeneratedOperationalBoundedPolynomialForwardEvaluationSourceLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9ePlus1NoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
