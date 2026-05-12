import CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q
import CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM5qRecheckCompletionStatus where
  | execBoundaryOperatorCompletedFromSM4qRecheck
  deriving DecidableEq, Repr

inductive SM5qRecheckNextPhaseStatus where
  | sm6bMayRecheckLevelStepExecMirror
  deriving DecidableEq, Repr

inductive SM5qRecheckNoFreeExecMatrixStatus where
  | noFreeExecMatrix
  deriving DecidableEq, Repr

inductive SM5qRecheckNoRealToRatReverseCastStatus where
  | noRealToRatReverseCast
  deriving DecidableEq, Repr

inductive SM5qRecheckNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM5qRecheckNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM5qRecheckNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM5qRecheckNoNewInverseOracleStatus where
  | noNewInverseOracle
  deriving DecidableEq, Repr

inductive SM5qRecheckNoProductIdentityProofStatus where
  | noProductIdentityProof
  deriving DecidableEq, Repr

inductive SM5qRecheckNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM5qRecheckNoNewInteriorEliminationCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM5qRecheckNoDtnMultiSchurRecomputationStatus where
  | noDtnGeneralizedDtnOrMultiSchurRecomputation
  deriving DecidableEq, Repr

inductive SM5qRecheckNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantOrHeegner
  deriving DecidableEq, Repr

structure GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
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
  sourceSM5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G
  sourceSM5q : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G
  sourceSM5q_source_eq_SM5 : sourceSM5q.sourceSM5 = sourceSM5
  sourceSM4qRecheck : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H
  sourceSM4qRecheck_source_eq_SM5_sourceMultiSchur :
    sourceSM4qRecheck.sourceSM4 = sourceSM5.sourceMultiSchur
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM5q : boundaryOperatorReal = sourceSM5q.boundaryOperatorReal
  execBoundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  execBoundaryOperator_eq_SM4qRecheck : execBoundaryOperator = sourceSM4qRecheck.execBoundaryOperator
  execBoundaryOperator_bridge_to_SM5 : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      ((sourceSM5.boundaryOperator i j : ℝ) : ℂ)
  entry_eq_SM4 : ∀ i j,
    boundaryOperatorReal i j = sourceSM5.sourceMultiSchur.boundaryOperator i j
  entry_eq_SM4qRecheck : ∀ i j,
    boundaryOperatorReal i j = sourceSM4qRecheck.sourceSM4.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  apply_eq_SM4 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM5.«apply» φ = sourceSM5.sourceMultiSchur.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM5.«apply» φ = boundaryOperatorReal.mulVec φ
  completionStatus : SM5qRecheckCompletionStatus
  completionStatus_eq :
    completionStatus = SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck
  nextPhaseStatus : SM5qRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM5qRecheckNextPhaseStatus.sm6bMayRecheckLevelStepExecMirror
  noFreeExecMatrixStatus : SM5qRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq : noFreeExecMatrixStatus = SM5qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatReverseCastStatus : SM5qRecheckNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM5qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM5qRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq : noScalarInverseStatus = SM5qRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM5qRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM5qRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM5qRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM5qRecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM5qRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM5qRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityProofStatus : SM5qRecheckNoProductIdentityProofStatus
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus = SM5qRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noTwoSidedInvStatus : SM5qRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM5qRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewInteriorEliminationCertificateStatus : SM5qRecheckNoNewInteriorEliminationCertificateStatus
  noNewInteriorEliminationCertificateStatus_eq :
    noNewInteriorEliminationCertificateStatus =
      SM5qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM5qRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM5qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM5qRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM5qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

namespace GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q

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

def fromSources
    (S5q : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G)
    (R4 : GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q Cell p A P wp W E K T M S H)
    (hR4 : R4.sourceSM4 = S5q.sourceSM5.sourceMultiSchur) :
    GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G where
  sourceSM5 := S5q.sourceSM5
  sourceSM5q := S5q
  sourceSM5q_source_eq_SM5 := by
    rfl
  sourceSM4qRecheck := R4
  sourceSM4qRecheck_source_eq_SM5_sourceMultiSchur := hR4
  boundaryOperatorReal := S5q.boundaryOperatorReal
  boundaryOperatorReal_eq_SM5q := by
    rfl
  execBoundaryOperator := R4.execBoundaryOperator
  execBoundaryOperator_eq_SM4qRecheck := by
    rfl
  execBoundaryOperator_bridge_to_SM5 := by
    intro i j
    calc
      ExecComplexBridge.toComplex (R4.execBoundaryOperator i j) =
          ((R4.sourceSM4.boundaryOperator i j : ℝ) : ℂ) :=
        R4.execBoundaryOperator_bridge_to_SM4 i j
      _ = ((S5q.sourceSM5.sourceMultiSchur.boundaryOperator i j : ℝ) : ℂ) := by
        rw [hR4]
      _ = ((S5q.sourceSM5.boundaryOperator i j : ℝ) : ℂ) := by
        rw [← S5q.sourceSM5.boundaryOperator_eq_SM4]
  entry_eq_SM4 := by
    intro i j
    exact S5q.entry_eq_SM4 i j
  entry_eq_SM4qRecheck := by
    intro i j
    calc
      S5q.boundaryOperatorReal i j = S5q.sourceSM5.sourceMultiSchur.boundaryOperator i j :=
        S5q.entry_eq_SM4 i j
      _ = R4.sourceSM4.boundaryOperator i j := by
        rw [← hR4]
  entry_eq_schur := by
    intro i j
    exact S5q.entry_eq_schur i j
  apply_eq_SM4 := by
    intro φ
    exact S5q.apply_eq_SM4 φ
  apply_eq_mulVec := by
    intro φ
    exact S5q.apply_eq_mulVec φ
  completionStatus := SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck
  completionStatus_eq := by
    rfl
  nextPhaseStatus := SM5qRecheckNextPhaseStatus.sm6bMayRecheckLevelStepExecMirror
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM5qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM5qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM5qRecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM5qRecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM5qRecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM5qRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus := SM5qRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM5qRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewInteriorEliminationCertificateStatus :=
    SM5qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noNewInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM5qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM5qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem sourceSM4qRecheck_source_from_SM5
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G) :
    X.sourceSM4qRecheck.sourceSM4 = X.sourceSM5.sourceMultiSchur :=
  X.sourceSM4qRecheck_source_eq_SM5_sourceMultiSchur

theorem execBoundaryOperator_bridge_to_SM5_thm
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (X.execBoundaryOperator i j) =
      ((X.sourceSM5.boundaryOperator i j : ℝ) : ℂ) :=
  X.execBoundaryOperator_bridge_to_SM5 i j

theorem entryReal_from_SM4qRecheck
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM4qRecheck.sourceSM4.boundaryOperator i j :=
  X.entry_eq_SM4qRecheck i j

theorem entryReal_from_SM5_SM4
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM5.sourceMultiSchur.boundaryOperator i j :=
  X.entry_eq_SM4 i j

theorem entryReal_from_schur
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          X.sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j :=
  X.entry_eq_schur i j

theorem apply_from_SM4
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM5.«apply» φ = X.sourceSM5.sourceMultiSchur.«apply» φ :=
  X.apply_eq_SM4 φ

theorem apply_from_boundaryOperatorReal_mulVec
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM5.«apply» φ = X.boundaryOperatorReal.mulVec φ :=
  X.apply_eq_mulVec φ

theorem completion_closed_from_SM4qRecheck
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G) :
    X.completionStatus = SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck :=
  X.completionStatus_eq

theorem next_phase_is_SM6b_recheck
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G) :
    X.nextPhaseStatus = SM5qRecheckNextPhaseStatus.sm6bMayRecheckLevelStepExecMirror :=
  X.nextPhaseStatus_eq

theorem no_forbidden_shortcuts
    (X : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G) :
    X.noFreeExecMatrixStatus = SM5qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    X.noRealToRatReverseCastStatus = SM5qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast ∧
    X.noScalarInverseStatus = SM5qRecheckNoScalarInverseStatus.noScalarInverse ∧
    X.noMatrixInvStatus = SM5qRecheckNoMatrixInvStatus.noMatrixInv ∧
    X.noFieldSimpStatus = SM5qRecheckNoFieldSimpStatus.noFieldSimp ∧
    X.noNewInverseOracleStatus = SM5qRecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    X.noProductIdentityProofStatus = SM5qRecheckNoProductIdentityProofStatus.noProductIdentityProof ∧
    X.noTwoSidedInvStatus = SM5qRecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    X.noNewInteriorEliminationCertificateStatus =
      SM5qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate ∧
    X.noDtnMultiSchurRecomputationStatus =
      SM5qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation ∧
    X.noCharpolyDiscriminantHeegnerStatus =
      SM5qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
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

end GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q

def regularGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      (sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger L).regularMultiSchur :=
  GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q.fromSources
    (regularGeneratedArithmeticSourceExecBoundaryOperatorSM5q
      (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L))
    (regularGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q L)
    (by rfl)

def variableGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      (sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger L).variableMultiSchur :=
  GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q.fromSources
    (variableGeneratedArithmeticSourceExecBoundaryOperatorSM5q
      (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L))
    (variableGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q L)
    (by rfl)

structure SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM5qLedger : SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger b β p regularWeight variableWeight
  sourceSM4qRecheckLedger : SM4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM5qLedger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableSource :
    GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM5qLedger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularExecBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularSource.execBoundaryOperator i j) =
      ((regularSource.sourceSM5.boundaryOperator i j : ℝ) : ℂ)
  variableExecBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableSource.execBoundaryOperator i j) =
      ((variableSource.sourceSM5.boundaryOperator i j : ℝ) : ℂ)
  regularSourceSM4qRecheck_eq_SM5Source :
    regularSource.sourceSM4qRecheck.sourceSM4 = regularSource.sourceSM5.sourceMultiSchur
  variableSourceSM4qRecheck_eq_SM5Source :
    variableSource.sourceSM4qRecheck.sourceSM4 = variableSource.sourceSM5.sourceMultiSchur
  regularCompletionStatus : SM5qRecheckCompletionStatus
  regularCompletionStatus_eq :
    regularCompletionStatus = SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck
  variableCompletionStatus : SM5qRecheckCompletionStatus
  variableCompletionStatus_eq :
    variableCompletionStatus = SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck
  nextPhaseStatus : SM5qRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM5qRecheckNextPhaseStatus.sm6bMayRecheckLevelStepExecMirror
  noFreeExecMatrixStatus : SM5qRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq : noFreeExecMatrixStatus = SM5qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatReverseCastStatus : SM5qRecheckNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM5qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM5qRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq : noScalarInverseStatus = SM5qRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM5qRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM5qRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM5qRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM5qRecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM5qRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM5qRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityProofStatus : SM5qRecheckNoProductIdentityProofStatus
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus = SM5qRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noTwoSidedInvStatus : SM5qRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM5qRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewInteriorEliminationCertificateStatus : SM5qRecheckNoNewInteriorEliminationCertificateStatus
  noNewInteriorEliminationCertificateStatus_eq :
    noNewInteriorEliminationCertificateStatus =
      SM5qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM5qRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM5qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM5qRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM5qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

def sm5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger b β p regularWeight variableWeight where
  sourceSM5qLedger :=
    sm5qGeneratedArithmeticSourceExecBoundaryOperatorLedger
      (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L)
  sourceSM4qRecheckLedger := sm4qRecheckGeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusLedger L
  regularSource := regularGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L
  variableSource := variableGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L
  regularExecBoundaryOperatorBridge := by
    intro i j
    exact (regularGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L).execBoundaryOperator_bridge_to_SM5 i j
  variableExecBoundaryOperatorBridge := by
    intro i j
    exact (variableGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L).execBoundaryOperator_bridge_to_SM5 i j
  regularSourceSM4qRecheck_eq_SM5Source := by
    exact (regularGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L).sourceSM4qRecheck_source_eq_SM5_sourceMultiSchur
  variableSourceSM4qRecheck_eq_SM5Source := by
    exact (variableGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L).sourceSM4qRecheck_source_eq_SM5_sourceMultiSchur
  regularCompletionStatus := SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck
  regularCompletionStatus_eq := by
    rfl
  variableCompletionStatus := SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck
  variableCompletionStatus_eq := by
    rfl
  nextPhaseStatus := SM5qRecheckNextPhaseStatus.sm6bMayRecheckLevelStepExecMirror
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM5qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM5qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM5qRecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM5qRecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM5qRecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM5qRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus := SM5qRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM5qRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewInteriorEliminationCertificateStatus :=
    SM5qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noNewInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM5qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM5qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem sm5qRecheck_regularCompletion_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger b β p regularWeight variableWeight) :
    L.regularCompletionStatus =
      SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck :=
  L.regularCompletionStatus_eq

theorem sm5qRecheck_variableCompletion_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger b β p regularWeight variableWeight) :
    L.variableCompletionStatus =
      SM5qRecheckCompletionStatus.execBoundaryOperatorCompletedFromSM4qRecheck :=
  L.variableCompletionStatus_eq

theorem sm5qRecheck_nextPhase_is_SM6b_recheck
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM5qRecheckNextPhaseStatus.sm6bMayRecheckLevelStepExecMirror :=
  L.nextPhaseStatus_eq

theorem sm5qRecheck_noForbiddenShortcuts
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger b β p regularWeight variableWeight) :
    L.noFreeExecMatrixStatus = SM5qRecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    L.noRealToRatReverseCastStatus = SM5qRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast ∧
    L.noScalarInverseStatus = SM5qRecheckNoScalarInverseStatus.noScalarInverse ∧
    L.noMatrixInvStatus = SM5qRecheckNoMatrixInvStatus.noMatrixInv ∧
    L.noFieldSimpStatus = SM5qRecheckNoFieldSimpStatus.noFieldSimp ∧
    L.noNewInverseOracleStatus = SM5qRecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    L.noProductIdentityProofStatus = SM5qRecheckNoProductIdentityProofStatus.noProductIdentityProof ∧
    L.noTwoSidedInvStatus = SM5qRecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    L.noNewInteriorEliminationCertificateStatus =
      SM5qRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate ∧
    L.noDtnMultiSchurRecomputationStatus =
      SM5qRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation ∧
    L.noCharpolyDiscriminantHeegnerStatus =
      SM5qRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
  ⟨L.noFreeExecMatrixStatus_eq,
   L.noRealToRatReverseCastStatus_eq,
   L.noScalarInverseStatus_eq,
   L.noMatrixInvStatus_eq,
   L.noFieldSimpStatus_eq,
   L.noNewInverseOracleStatus_eq,
   L.noProductIdentityProofStatus_eq,
   L.noTwoSidedInvStatus_eq,
   L.noNewInteriorEliminationCertificateStatus_eq,
   L.noDtnMultiSchurRecomputationStatus_eq,
   L.noCharpolyDiscriminantHeegnerStatus_eq⟩

end Smoke

end CNNA.PillarA.Arithmetic
