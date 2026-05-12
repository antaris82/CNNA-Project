import CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q
import CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM4qRecheckCompletionStatus where
  | execBoundaryOperatorCompletedFromSM3fqPlus
  deriving DecidableEq, Repr

inductive SM4qRecheckNextPhaseStatus where
  | sm5qMayRecheckArithmeticExecBoundaryOperator
  deriving DecidableEq, Repr

inductive SM4qRecheckNoFreeExecMatrixStatus where
  | noFreeExecMatrix
  deriving DecidableEq, Repr

inductive SM4qRecheckNoRealToRatReverseCastStatus where
  | noRealToRatReverseCast
  deriving DecidableEq, Repr

inductive SM4qRecheckNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM4qRecheckNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM4qRecheckNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM4qRecheckNoNewInverseOracleStatus where
  | noNewInverseOracle
  deriving DecidableEq, Repr

inductive SM4qRecheckNoProductIdentityProofStatus where
  | noProductIdentityProof
  deriving DecidableEq, Repr

inductive SM4qRecheckNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM4qRecheckNoNewInteriorEliminationCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM4qRecheckNoDtnMultiSchurRecomputationStatus where
  | noDtnGeneralizedDtnOrMultiSchurRecomputation
  deriving DecidableEq, Repr

inductive SM4qRecheckNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantOrHeegner
  deriving DecidableEq, Repr

theorem sourceSM3fq_boundaryOperatorReal_eq_SM4BoundaryOperator_from_SM3fqPlus
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (Q : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (C : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H) :
    C.sourceSM3fq.boundaryOperatorReal = Q.sourceSM4.boundaryOperator := by
  calc
    C.sourceSM3fq.boundaryOperatorReal =
        generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
            generatedInteriorBoundaryBlockSM3fR W :=
      C.sourceSM3fqBoundaryOperatorReal_eq_handoffSchur
    _ = generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W *
            Q.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
            generatedInteriorBoundaryBlockSM3fR W := by
      rw [← Q.certificate_inverseMatrix_eq_handoffCandidate]
    _ = Q.sourceSM4.boundaryOperator :=
      Q.sourceSM4.boundaryOperator_eq_schur.symm

structure GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) where
  sourceSM4 : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H
  sourceSM4q : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H
  sourceSM4q_source_eq_SM4 : sourceSM4q.sourceSM4 = sourceSM4
  sourceSM3fqPlus : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM4 : boundaryOperatorReal = sourceSM4.boundaryOperator
  execBoundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  execBoundaryOperator_eq_SM3fqPlus : execBoundaryOperator = sourceSM3fqPlus.boundaryOperatorExec
  sourceSM3fqBoundaryOperatorReal_eq_SM4 :
    sourceSM3fqPlus.sourceSM3fq.boundaryOperatorReal = sourceSM4.boundaryOperator
  execBoundaryOperator_bridge_to_SM4 : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      ((sourceSM4.boundaryOperator i j : ℝ) : ℂ)
  entry_eq_SM3iR : ∀ i j,
    boundaryOperatorReal i j =
      sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator i j
  entry_eq_topBoundary : ∀ i j,
    boundaryOperatorReal i j = sourceSM4.sourceTopBoundaryDtN.boundaryOperator i j
  entry_eq_certificate : ∀ i j,
    boundaryOperatorReal i j =
      sourceSM4.sourceInteriorEliminationCertificate.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  certificate_inverseMatrix_eq_handoffCandidate :
    sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix
  apply_eq_SM3iR : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM4.«apply» φ =
      sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM4.«apply» φ = boundaryOperatorReal.mulVec φ
  completionStatus : SM4qRecheckCompletionStatus
  completionStatus_eq :
    completionStatus = SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus
  nextPhaseStatus : SM4qRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM4qRecheckNextPhaseStatus.sm5qMayRecheckArithmeticExecBoundaryOperator
  noFreeExecMatrixStatus : SM4qRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq : noFreeExecMatrixStatus = SM4qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatReverseCastStatus : SM4qRecheckNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM4qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM4qRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq : noScalarInverseStatus = SM4qRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM4qRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM4qRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM4qRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM4qRecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM4qRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM4qRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityProofStatus : SM4qRecheckNoProductIdentityProofStatus
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus = SM4qRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noTwoSidedInvStatus : SM4qRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM4qRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewInteriorEliminationCertificateStatus : SM4qRecheckNoNewInteriorEliminationCertificateStatus
  noNewInteriorEliminationCertificateStatus_eq :
    noNewInteriorEliminationCertificateStatus =
      SM4qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM4qRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM4qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM4qRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM4qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

namespace GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q

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

def fromSources
    (Q : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (C : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H) :
    GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H where
  sourceSM4 := Q.sourceSM4
  sourceSM4q := Q
  sourceSM4q_source_eq_SM4 := by
    rfl
  sourceSM3fqPlus := C
  boundaryOperatorReal := Q.boundaryOperatorReal
  boundaryOperatorReal_eq_SM4 := by
    exact Q.boundaryOperatorReal_eq_SM4
  execBoundaryOperator := C.boundaryOperatorExec
  execBoundaryOperator_eq_SM3fqPlus := by
    rfl
  sourceSM3fqBoundaryOperatorReal_eq_SM4 := by
    exact sourceSM3fq_boundaryOperatorReal_eq_SM4BoundaryOperator_from_SM3fqPlus Q C
  execBoundaryOperator_bridge_to_SM4 := by
    intro i j
    calc
      ExecComplexBridge.toComplex (C.boundaryOperatorExec i j) =
          ((C.sourceSM3fq.boundaryOperatorReal i j : ℝ) : ℂ) :=
        C.boundaryOperatorExec_bridge_to_SM3fSchur i j
      _ = ((Q.sourceSM4.boundaryOperator i j : ℝ) : ℂ) := by
        rw [sourceSM3fq_boundaryOperatorReal_eq_SM4BoundaryOperator_from_SM3fqPlus Q C]
  entry_eq_SM3iR := by
    intro i j
    exact Q.entry_eq_SM3iR i j
  entry_eq_topBoundary := by
    intro i j
    exact Q.entry_eq_topBoundary i j
  entry_eq_certificate := by
    intro i j
    exact Q.entry_eq_certificate i j
  entry_eq_schur := by
    intro i j
    exact Q.entry_eq_schur i j
  certificate_inverseMatrix_eq_handoffCandidate := by
    exact Q.certificate_inverseMatrix_eq_handoffCandidate
  apply_eq_SM3iR := by
    intro φ
    exact Q.apply_eq_SM3iR φ
  apply_eq_mulVec := by
    intro φ
    exact Q.apply_eq_mulVec φ
  completionStatus := SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus
  completionStatus_eq := by
    rfl
  nextPhaseStatus := SM4qRecheckNextPhaseStatus.sm5qMayRecheckArithmeticExecBoundaryOperator
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM4qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM4qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM4qRecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM4qRecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM4qRecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM4qRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus := SM4qRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM4qRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewInteriorEliminationCertificateStatus :=
    SM4qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noNewInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM4qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM4qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem execBoundaryOperator_bridge_to_SM4_thm
    (X : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (X.execBoundaryOperator i j) =
      ((X.sourceSM4.boundaryOperator i j : ℝ) : ℂ) :=
  X.execBoundaryOperator_bridge_to_SM4 i j

theorem sourceSM3fq_boundaryOperatorReal_from_SM4
    (X : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H) :
    X.sourceSM3fqPlus.sourceSM3fq.boundaryOperatorReal = X.sourceSM4.boundaryOperator :=
  X.sourceSM3fqBoundaryOperatorReal_eq_SM4

theorem completion_closed_from_SM3fqPlus
    (X : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H) :
    X.completionStatus = SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus :=
  X.completionStatus_eq

theorem next_phase_is_SM5q_recheck
    (X : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H) :
    X.nextPhaseStatus = SM4qRecheckNextPhaseStatus.sm5qMayRecheckArithmeticExecBoundaryOperator :=
  X.nextPhaseStatus_eq

theorem no_forbidden_shortcuts
    (X : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H) :
    X.noFreeExecMatrixStatus = SM4qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    X.noRealToRatReverseCastStatus = SM4qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast ∧
    X.noScalarInverseStatus = SM4qRecheckNoScalarInverseStatus.noScalarInverse ∧
    X.noMatrixInvStatus = SM4qRecheckNoMatrixInvStatus.noMatrixInv ∧
    X.noFieldSimpStatus = SM4qRecheckNoFieldSimpStatus.noFieldSimp ∧
    X.noNewInverseOracleStatus = SM4qRecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    X.noProductIdentityProofStatus = SM4qRecheckNoProductIdentityProofStatus.noProductIdentityProof ∧
    X.noTwoSidedInvStatus = SM4qRecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    X.noNewInteriorEliminationCertificateStatus =
      SM4qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate ∧
    X.noDtnMultiSchurRecomputationStatus =
      SM4qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation ∧
    X.noCharpolyDiscriminantHeegnerStatus =
      SM4qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
  ⟨X.noFreeExecMatrixStatus_eq,
   X.noRealToRatReverseCastStatus_eq,
   X.noScalarInverseStatus_eq,
   X.noMatrixInvStatus_eq,
   X.noFieldSimpStatus_eq,
   X.noNewInverseOracleStatus_eq,
   X.noProductIdentityProofStatus_eq,
   X.noTwoSidedInvStatus_eq,
   X.noNewInteriorEliminationCertificateStatus_eq,
   X.noDtnMultiSchurRecomputationStatus_eq,
   X.noCharpolyDiscriminantHeegnerStatus_eq⟩

end GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q

def regularGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q.fromSources
    (regularGeneratedMultiSchurExecBoundaryOperatorSM4q
      (sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger L))
    (regularGeneratedSM3fSchurExecCompletionSM3fqPlus L)

def variableGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q.fromSources
    (variableGeneratedMultiSchurExecBoundaryOperatorSM4q
      (sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger L))
    (variableGeneratedSM3fSchurExecCompletionSM3fqPlus L)

structure SM4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM4qLedger : SM4qGeneratedMultiSchurExecBoundaryOperatorLedger b β p regularWeight variableWeight
  sourceSM3fqPlusLedger : SM3fqPlusGeneratedSM3fSchurExecCompletionLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableSource :
    GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularSource_eq_main :
    regularSource =
      regularGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
        sourceSM3fqPlusLedger.sourceSM3fqLedger.sourceSM3fLedger
  variableSource_eq_main :
    variableSource =
      variableGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q
        sourceSM3fqPlusLedger.sourceSM3fqLedger.sourceSM3fLedger
  regularExecBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularSource.execBoundaryOperator i j) =
      ((regularSource.sourceSM4.boundaryOperator i j : ℝ) : ℂ)
  variableExecBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableSource.execBoundaryOperator i j) =
      ((variableSource.sourceSM4.boundaryOperator i j : ℝ) : ℂ)
  regularCompletionStatus : SM4qRecheckCompletionStatus
  regularCompletionStatus_eq :
    regularCompletionStatus = SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus
  variableCompletionStatus : SM4qRecheckCompletionStatus
  variableCompletionStatus_eq :
    variableCompletionStatus = SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus
  nextPhaseStatus : SM4qRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM4qRecheckNextPhaseStatus.sm5qMayRecheckArithmeticExecBoundaryOperator

def sm4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger b β p regularWeight variableWeight where
  sourceSM4qLedger :=
    sm4qGeneratedMultiSchurExecBoundaryOperatorLedger
      (sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger L)
  sourceSM3fqPlusLedger := sm3fqPlusGeneratedSM3fSchurExecCompletionLedger L
  regularSource := regularGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q L
  variableSource := variableGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q L
  regularSource_eq_main := by
    rfl
  variableSource_eq_main := by
    rfl
  regularExecBoundaryOperatorBridge := by
    intro i j
    exact (regularGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q L).execBoundaryOperator_bridge_to_SM4 i j
  variableExecBoundaryOperatorBridge := by
    intro i j
    exact (variableGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q L).execBoundaryOperator_bridge_to_SM4 i j
  regularCompletionStatus := SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus
  regularCompletionStatus_eq := by
    rfl
  variableCompletionStatus := SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus
  variableCompletionStatus_eq := by
    rfl
  nextPhaseStatus := SM4qRecheckNextPhaseStatus.sm5qMayRecheckArithmeticExecBoundaryOperator
  nextPhaseStatus_eq := by
    rfl

theorem sm4qRecheck_regularCompletion_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger b β p regularWeight variableWeight) :
    L.regularCompletionStatus =
      SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus :=
  L.regularCompletionStatus_eq

theorem sm4qRecheck_variableCompletion_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger b β p regularWeight variableWeight) :
    L.variableCompletionStatus =
      SM4qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM3fqPlus :=
  L.variableCompletionStatus_eq

theorem sm4qRecheck_nextPhase_is_SM5q_recheck
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM4qRecheckNextPhaseStatus.sm5qMayRecheckArithmeticExecBoundaryOperator :=
  L.nextPhaseStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
