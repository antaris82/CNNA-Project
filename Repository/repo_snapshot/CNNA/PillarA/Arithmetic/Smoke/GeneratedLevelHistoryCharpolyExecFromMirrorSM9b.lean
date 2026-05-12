import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
import CNNA.PillarA.Arithmetic.Schur.CharpolyExec

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM9bCompletionStatus where
  | determinantAndPencilEvaluationClosedFromSM9aRecheckMirror
  deriving DecidableEq, Repr

inductive SM9bConsumedMirrorStatus where
  | consumedComputedSM9aRecheckExecMirror
  deriving DecidableEq, Repr

inductive SM9bNextPhaseStatus where
  | sm9cMayConsumeCharpolyEvaluation
  deriving DecidableEq, Repr

inductive SM9bNoFreeMatrixStatus where
  | noFreeMatrix
  deriving DecidableEq, Repr

inductive SM9bNoFreeCharpolyPolynomialStatus where
  | noFreeCharpolyPolynomial
  deriving DecidableEq, Repr

inductive SM9bNoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9bNoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9bNoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9bNoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9bNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9bNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9bNoNewTwoSidedInvStatus where
  | noNewTwoSidedInv
  deriving DecidableEq, Repr

inductive SM9bNoNewCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM9bNoDtnMultiSchurRecomputationStatus where
  | noDtnMultiSchurRecomputation
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

abbrev GeneratedLevelHistoryCharpolyExecIndexSM9b
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G) :=
  GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8Recheck.sourceSM8

def generatedLevelHistorySpectralPencilSM9b
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    Matrix (GeneratedLevelHistoryCharpolyExecIndexSM9b Z)
      (GeneratedLevelHistoryCharpolyExecIndexSM9b Z) ExecComplex :=
  Schur.spectralPencil Z.execMatrix z

def generatedLevelHistoryOperativeDeterminantSM9b
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) : ExecComplex :=
  Schur.operativeDeterminant (generatedLevelHistorySpectralPencilSM9b Z z)

def generatedLevelHistoryCharpolyEvaluationSM9b
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) : ExecComplex :=
  Schur.operativeCharpolyEvaluation Z.execMatrix z

theorem generatedLevelHistorySpectralPencilSM9b_eq_from_matrix
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    generatedLevelHistorySpectralPencilSM9b Z z = Schur.spectralPencil Z.execMatrix z := by
  rfl

theorem generatedLevelHistoryOperativeDeterminantSM9b_eq_matrix_det
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    generatedLevelHistoryOperativeDeterminantSM9b Z z =
      Matrix.det (generatedLevelHistorySpectralPencilSM9b Z z) := by
  exact Schur.operativeDeterminant_eq_matrix_det (generatedLevelHistorySpectralPencilSM9b Z z)

theorem generatedLevelHistoryCharpolyEvaluationSM9b_eq_det_pencil
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    generatedLevelHistoryCharpolyEvaluationSM9b Z z =
      Matrix.det (generatedLevelHistorySpectralPencilSM9b Z z) := by
  exact Schur.operativeCharpolyEvaluation_eq_det_pencil Z.execMatrix z

theorem generatedLevelHistoryOperativeDeterminantSM9b_eq_charpolyEvaluation
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    generatedLevelHistoryOperativeDeterminantSM9b Z z =
      generatedLevelHistoryCharpolyEvaluationSM9b Z z := by
  rfl

structure GeneratedLevelHistoryCharpolyExecFromMirrorSM9b
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
  sourceSM9aRecheck :
    GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G
  z : Schur.SpectralParameter
  matrix : Matrix (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9aRecheck)
    (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9aRecheck) ExecComplex
  matrix_eq_SM9aRecheck : matrix = sourceSM9aRecheck.execMatrix
  spectralPencil : Matrix (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9aRecheck)
    (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9aRecheck) ExecComplex
  spectralPencil_eq_from_matrix : spectralPencil = Schur.spectralPencil matrix z
  determinant : ExecComplex
  determinant_eq_operative : determinant = Schur.operativeDeterminant spectralPencil
  determinant_eq_matrix_det : determinant = Matrix.det spectralPencil
  charpolyEvaluation : ExecComplex
  charpolyEvaluation_eq_operative : charpolyEvaluation = Schur.operativeCharpolyEvaluation matrix z
  charpolyEvaluation_eq_det_pencil : charpolyEvaluation = Matrix.det spectralPencil
  determinant_eq_charpolyEvaluation : determinant = charpolyEvaluation
  matrix_entry_from_SM9aRecheck : ∀ i j, matrix i j = sourceSM9aRecheck.execMatrix i j
  matrix_entry_from_SM8Recheck : ∀ i j, matrix i j = sourceSM9aRecheck.sourceSM8Recheck.execMatrix i j
  matrix_bridge_to_SM9aRecheck_entryReal : ∀ i j,
    ExecComplexBridge.toComplex (matrix i j) = (sourceSM9aRecheck.entryReal i j : ℂ)
  matrix_bridge_to_SM8Recheck_entryReal : ∀ i j,
    ExecComplexBridge.toComplex (matrix i j) = (sourceSM9aRecheck.sourceSM8Recheck.matrixReal i j : ℂ)
  matrix_entry_real_eq_SM8 : ∀ i j,
    sourceSM9aRecheck.entryReal i j = sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.matrix i j
  matrix_entry_real_eq_generatedLevelHistoryMatrix : ∀ i j,
    sourceSM9aRecheck.entryReal i j =
      generatedLevelHistoryMatrixSM8 sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge i j
  matrix_entry_real_eq_boundaryOperator : ∀ i j,
    sourceSM9aRecheck.entryReal i j =
      sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.boundaryOperator
        (sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j)
  matrix_entry_real_eq_schur : ∀ i j,
    sourceSM9aRecheck.entryReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j)
  completionStatus : SM9bCompletionStatus
  completionStatus_eq :
    completionStatus = SM9bCompletionStatus.determinantAndPencilEvaluationClosedFromSM9aRecheckMirror
  consumedMirrorStatus : SM9bConsumedMirrorStatus
  consumedMirrorStatus_eq :
    consumedMirrorStatus = SM9bConsumedMirrorStatus.consumedComputedSM9aRecheckExecMirror
  nextPhaseStatus : SM9bNextPhaseStatus
  nextPhaseStatus_eq : nextPhaseStatus = SM9bNextPhaseStatus.sm9cMayConsumeCharpolyEvaluation
  noFreeMatrixStatus : SM9bNoFreeMatrixStatus
  noFreeMatrixStatus_eq : noFreeMatrixStatus = SM9bNoFreeMatrixStatus.noFreeMatrix
  noFreeCharpolyPolynomialStatus : SM9bNoFreeCharpolyPolynomialStatus
  noFreeCharpolyPolynomialStatus_eq :
    noFreeCharpolyPolynomialStatus = SM9bNoFreeCharpolyPolynomialStatus.noFreeCharpolyPolynomial
  noFactorizationStatus : SM9bNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9bNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9bNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9bNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9bNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9bNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9bNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9bNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9bNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9bNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9bNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9bNoFieldSimpStatus.noFieldSimp
  noNewTwoSidedInvStatus : SM9bNoNewTwoSidedInvStatus
  noNewTwoSidedInvStatus_eq :
    noNewTwoSidedInvStatus = SM9bNoNewTwoSidedInvStatus.noNewTwoSidedInv
  noNewCertificateStatus : SM9bNoNewCertificateStatus
  noNewCertificateStatus_eq :
    noNewCertificateStatus = SM9bNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM9bNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM9bNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation

namespace GeneratedLevelHistoryCharpolyExecFromMirrorSM9b

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

def fromSM9aRecheck
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G where
  sourceSM9aRecheck := Z
  z := z
  matrix := Z.execMatrix
  matrix_eq_SM9aRecheck := by
    rfl
  spectralPencil := generatedLevelHistorySpectralPencilSM9b Z z
  spectralPencil_eq_from_matrix := by
    rfl
  determinant := generatedLevelHistoryOperativeDeterminantSM9b Z z
  determinant_eq_operative := by
    rfl
  determinant_eq_matrix_det := by
    exact generatedLevelHistoryOperativeDeterminantSM9b_eq_matrix_det Z z
  charpolyEvaluation := generatedLevelHistoryCharpolyEvaluationSM9b Z z
  charpolyEvaluation_eq_operative := by
    rfl
  charpolyEvaluation_eq_det_pencil := by
    exact generatedLevelHistoryCharpolyEvaluationSM9b_eq_det_pencil Z z
  determinant_eq_charpolyEvaluation := by
    exact generatedLevelHistoryOperativeDeterminantSM9b_eq_charpolyEvaluation Z z
  matrix_entry_from_SM9aRecheck := by
    intro i j
    rfl
  matrix_entry_from_SM8Recheck := by
    intro i j
    exact Z.execEntry_from_SM8Recheck i j
  matrix_bridge_to_SM9aRecheck_entryReal := by
    intro i j
    exact Z.execMatrix_bridge_to_SM9a i j
  matrix_bridge_to_SM8Recheck_entryReal := by
    intro i j
    exact Z.execMatrix_bridge_to_SM8Recheck i j
  matrix_entry_real_eq_SM8 := by
    intro i j
    exact Z.entryReal_eq_SM8 i j
  matrix_entry_real_eq_generatedLevelHistoryMatrix := by
    intro i j
    exact Z.entryReal_eq_generatedLevelHistoryMatrix i j
  matrix_entry_real_eq_boundaryOperator := by
    intro i j
    exact Z.entryReal_eq_boundaryOperator i j
  matrix_entry_real_eq_schur := by
    intro i j
    exact Z.entryReal_eq_schur i j
  completionStatus := SM9bCompletionStatus.determinantAndPencilEvaluationClosedFromSM9aRecheckMirror
  completionStatus_eq := by
    rfl
  consumedMirrorStatus := SM9bConsumedMirrorStatus.consumedComputedSM9aRecheckExecMirror
  consumedMirrorStatus_eq := by
    rfl
  nextPhaseStatus := SM9bNextPhaseStatus.sm9cMayConsumeCharpolyEvaluation
  nextPhaseStatus_eq := by
    rfl
  noFreeMatrixStatus := SM9bNoFreeMatrixStatus.noFreeMatrix
  noFreeMatrixStatus_eq := by
    rfl
  noFreeCharpolyPolynomialStatus := SM9bNoFreeCharpolyPolynomialStatus.noFreeCharpolyPolynomial
  noFreeCharpolyPolynomialStatus_eq := by
    rfl
  noFactorizationStatus := SM9bNoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9bNoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9bNoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9bNoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9bNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9bNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewTwoSidedInvStatus := SM9bNoNewTwoSidedInvStatus.noNewTwoSidedInv
  noNewTwoSidedInvStatus_eq := by
    rfl
  noNewCertificateStatus := SM9bNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noNewCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM9bNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl

theorem matrix_from_SM9aRecheck
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.matrix = C.sourceSM9aRecheck.execMatrix :=
  C.matrix_eq_SM9aRecheck

theorem spectralPencil_from_matrix
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.spectralPencil = Schur.spectralPencil C.matrix C.z :=
  C.spectralPencil_eq_from_matrix

theorem determinant_from_matrix_det
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.determinant = Matrix.det C.spectralPencil :=
  C.determinant_eq_matrix_det

theorem charpolyEvaluation_from_det_pencil
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.charpolyEvaluation = Matrix.det C.spectralPencil :=
  C.charpolyEvaluation_eq_det_pencil

theorem determinant_from_charpolyEvaluation
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.determinant = C.charpolyEvaluation :=
  C.determinant_eq_charpolyEvaluation

theorem matrix_entry_from_SM9aRecheck_thm
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryCharpolyExecIndexSM9b C.sourceSM9aRecheck) :
    C.matrix i j = C.sourceSM9aRecheck.execMatrix i j :=
  C.matrix_entry_from_SM9aRecheck i j

theorem matrix_bridge_to_entryReal
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryCharpolyExecIndexSM9b C.sourceSM9aRecheck) :
    ExecComplexBridge.toComplex (C.matrix i j) = (C.sourceSM9aRecheck.entryReal i j : ℂ) :=
  C.matrix_bridge_to_SM9aRecheck_entryReal i j

theorem entryReal_from_schur
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryCharpolyExecIndexSM9b C.sourceSM9aRecheck) :
    C.sourceSM9aRecheck.entryReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          C.sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (C.sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (C.sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j) :=
  C.matrix_entry_real_eq_schur i j

theorem computation_closed
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.completionStatus =
      SM9bCompletionStatus.determinantAndPencilEvaluationClosedFromSM9aRecheckMirror :=
  C.completionStatus_eq

theorem nextPhase_SM9c_may_consume
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.nextPhaseStatus = SM9bNextPhaseStatus.sm9cMayConsumeCharpolyEvaluation :=
  C.nextPhaseStatus_eq

theorem no_forbidden_shortcuts
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    C.noFreeMatrixStatus = SM9bNoFreeMatrixStatus.noFreeMatrix ∧
    C.noFreeCharpolyPolynomialStatus = SM9bNoFreeCharpolyPolynomialStatus.noFreeCharpolyPolynomial ∧
    C.noFactorizationStatus = SM9bNoFactorizationStatus.noFactorization ∧
    C.noDiscriminantStatus = SM9bNoDiscriminantStatus.noDiscriminant ∧
    C.noHeegnerTargetStatus = SM9bNoHeegnerTargetStatus.noHeegnerTarget ∧
    C.noCMTargetStatus = SM9bNoCMTargetStatus.noCMTarget ∧
    C.noMatrixInvStatus = SM9bNoMatrixInvStatus.noMatrixInv ∧
    C.noFieldSimpStatus = SM9bNoFieldSimpStatus.noFieldSimp ∧
    C.noNewTwoSidedInvStatus = SM9bNoNewTwoSidedInvStatus.noNewTwoSidedInv ∧
    C.noNewCertificateStatus = SM9bNoNewCertificateStatus.noNewInteriorEliminationCertificate ∧
    C.noDtnMultiSchurRecomputationStatus =
      SM9bNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation :=
  ⟨C.noFreeMatrixStatus_eq,
   C.noFreeCharpolyPolynomialStatus_eq,
   C.noFactorizationStatus_eq,
   C.noDiscriminantStatus_eq,
   C.noHeegnerTargetStatus_eq,
   C.noCMTargetStatus_eq,
   C.noMatrixInvStatus_eq,
   C.noFieldSimpStatus_eq,
   C.noNewTwoSidedInvStatus_eq,
   C.noNewCertificateStatus_eq,
   C.noDtnMultiSchurRecomputationStatus_eq⟩

end GeneratedLevelHistoryCharpolyExecFromMirrorSM9b

def regularGeneratedLevelHistoryCharpolyExecFromMirrorSM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (z : Schur.SpectralParameter) :
    GeneratedLevelHistoryCharpolyExecFromMirrorSM9b
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryCharpolyExecFromMirrorSM9b.fromSM9aRecheck L.regularSource z

def variableGeneratedLevelHistoryCharpolyExecFromMirrorSM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (z : Schur.SpectralParameter) :
    GeneratedLevelHistoryCharpolyExecFromMirrorSM9b
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryCharpolyExecFromMirrorSM9b.fromSM9aRecheck L.variableSource z

structure SM9bGeneratedLevelHistoryCharpolyExecLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9aRecheckLedger :
    SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight
  regularCharpoly :
    GeneratedLevelHistoryCharpolyExecFromMirrorSM9b
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableCharpoly :
    GeneratedLevelHistoryCharpolyExecFromMirrorSM9b
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularCharpoly_eq_from_SM9aRecheck :
    regularCharpoly = regularGeneratedLevelHistoryCharpolyExecFromMirrorSM9b sourceSM9aRecheckLedger z
  variableCharpoly_eq_from_SM9aRecheck :
    variableCharpoly = variableGeneratedLevelHistoryCharpolyExecFromMirrorSM9b sourceSM9aRecheckLedger z
  regularCharpolyEvaluation_eq_det_pencil :
    regularCharpoly.charpolyEvaluation = Matrix.det regularCharpoly.spectralPencil
  variableCharpolyEvaluation_eq_det_pencil :
    variableCharpoly.charpolyEvaluation = Matrix.det variableCharpoly.spectralPencil
  regularDeterminant_eq_charpolyEvaluation :
    regularCharpoly.determinant = regularCharpoly.charpolyEvaluation
  variableDeterminant_eq_charpolyEvaluation :
    variableCharpoly.determinant = variableCharpoly.charpolyEvaluation
  regularMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularCharpoly.matrix i j) =
      (regularCharpoly.sourceSM9aRecheck.entryReal i j : ℂ)
  variableMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableCharpoly.matrix i j) =
      (variableCharpoly.sourceSM9aRecheck.entryReal i j : ℂ)
  completionStatus : SM9bCompletionStatus
  completionStatus_eq :
    completionStatus = SM9bCompletionStatus.determinantAndPencilEvaluationClosedFromSM9aRecheckMirror
  consumedMirrorStatus : SM9bConsumedMirrorStatus
  consumedMirrorStatus_eq :
    consumedMirrorStatus = SM9bConsumedMirrorStatus.consumedComputedSM9aRecheckExecMirror
  nextPhaseStatus : SM9bNextPhaseStatus
  nextPhaseStatus_eq : nextPhaseStatus = SM9bNextPhaseStatus.sm9cMayConsumeCharpolyEvaluation
  noFreeMatrixStatus : SM9bNoFreeMatrixStatus
  noFreeMatrixStatus_eq : noFreeMatrixStatus = SM9bNoFreeMatrixStatus.noFreeMatrix
  noFreeCharpolyPolynomialStatus : SM9bNoFreeCharpolyPolynomialStatus
  noFreeCharpolyPolynomialStatus_eq :
    noFreeCharpolyPolynomialStatus = SM9bNoFreeCharpolyPolynomialStatus.noFreeCharpolyPolynomial
  noFactorizationStatus : SM9bNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9bNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9bNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9bNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9bNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9bNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9bNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9bNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9bNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9bNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9bNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9bNoFieldSimpStatus.noFieldSimp
  noNewTwoSidedInvStatus : SM9bNoNewTwoSidedInvStatus
  noNewTwoSidedInvStatus_eq :
    noNewTwoSidedInvStatus = SM9bNoNewTwoSidedInvStatus.noNewTwoSidedInv
  noNewCertificateStatus : SM9bNoNewCertificateStatus
  noNewCertificateStatus_eq :
    noNewCertificateStatus = SM9bNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM9bNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM9bNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation

def sm9bGeneratedLevelHistoryCharpolyExecLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (z : Schur.SpectralParameter) :
    SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z :=
  let R := regularGeneratedLevelHistoryCharpolyExecFromMirrorSM9b L z
  let V := variableGeneratedLevelHistoryCharpolyExecFromMirrorSM9b L z
  { sourceSM9aRecheckLedger := L
    regularCharpoly := R
    variableCharpoly := V
    regularCharpoly_eq_from_SM9aRecheck := by
      rfl
    variableCharpoly_eq_from_SM9aRecheck := by
      rfl
    regularCharpolyEvaluation_eq_det_pencil := R.charpolyEvaluation_eq_det_pencil
    variableCharpolyEvaluation_eq_det_pencil := V.charpolyEvaluation_eq_det_pencil
    regularDeterminant_eq_charpolyEvaluation := R.determinant_eq_charpolyEvaluation
    variableDeterminant_eq_charpolyEvaluation := V.determinant_eq_charpolyEvaluation
    regularMatrixBridge := by
      intro i j
      exact R.matrix_bridge_to_SM9aRecheck_entryReal i j
    variableMatrixBridge := by
      intro i j
      exact V.matrix_bridge_to_SM9aRecheck_entryReal i j
    completionStatus := SM9bCompletionStatus.determinantAndPencilEvaluationClosedFromSM9aRecheckMirror
    completionStatus_eq := by
      rfl
    consumedMirrorStatus := SM9bConsumedMirrorStatus.consumedComputedSM9aRecheckExecMirror
    consumedMirrorStatus_eq := by
      rfl
    nextPhaseStatus := SM9bNextPhaseStatus.sm9cMayConsumeCharpolyEvaluation
    nextPhaseStatus_eq := by
      rfl
    noFreeMatrixStatus := SM9bNoFreeMatrixStatus.noFreeMatrix
    noFreeMatrixStatus_eq := by
      rfl
    noFreeCharpolyPolynomialStatus := SM9bNoFreeCharpolyPolynomialStatus.noFreeCharpolyPolynomial
    noFreeCharpolyPolynomialStatus_eq := by
      rfl
    noFactorizationStatus := SM9bNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9bNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9bNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9bNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9bNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9bNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noNewTwoSidedInvStatus := SM9bNoNewTwoSidedInvStatus.noNewTwoSidedInv
    noNewTwoSidedInvStatus_eq := by
      rfl
    noNewCertificateStatus := SM9bNoNewCertificateStatus.noNewInteriorEliminationCertificate
    noNewCertificateStatus_eq := by
      rfl
    noDtnMultiSchurRecomputationStatus :=
      SM9bNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
    noDtnMultiSchurRecomputationStatus_eq := by
      rfl }

def sm9bGeneratedLevelHistoryCharpolyExecLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level)
    (z : Schur.SpectralParameter) :
    SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z :=
  sm9bGeneratedLevelHistoryCharpolyExecLedger
    (sm9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger_from_accumulatedEntryCancellationLedger
      L level levelIndex) z

theorem sm9b_regularCharpolyEvaluation_eq_det_pencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    L.regularCharpoly.charpolyEvaluation = Matrix.det L.regularCharpoly.spectralPencil :=
  L.regularCharpolyEvaluation_eq_det_pencil

theorem sm9b_variableCharpolyEvaluation_eq_det_pencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    L.variableCharpoly.charpolyEvaluation = Matrix.det L.variableCharpoly.spectralPencil :=
  L.variableCharpolyEvaluation_eq_det_pencil

theorem sm9b_nextPhase_SM9c
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9bNextPhaseStatus.sm9cMayConsumeCharpolyEvaluation :=
  L.nextPhaseStatus_eq

theorem sm9b_noFactorization
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    L.noFactorizationStatus = SM9bNoFactorizationStatus.noFactorization :=
  L.noFactorizationStatus_eq

theorem sm9b_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9bNoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

theorem sm9b_noHeegnerTarget
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    L.noHeegnerTargetStatus = SM9bNoHeegnerTargetStatus.noHeegnerTarget :=
  L.noHeegnerTargetStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
