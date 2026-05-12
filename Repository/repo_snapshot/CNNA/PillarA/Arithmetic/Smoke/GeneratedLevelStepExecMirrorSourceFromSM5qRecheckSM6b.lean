import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b
import CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM6bRecheckCompletionStatus where
  | execMirrorCompletedFromSM5qRecheck
  deriving DecidableEq, Repr

inductive SM6bRecheckNextPhaseStatus where
  | sm8MayConsumeLevelStepExecMirror
  deriving DecidableEq, Repr

inductive SM6bRecheckNoFreeExecMatrixStatus where
  | noFreeExecMatrix
  deriving DecidableEq, Repr

inductive SM6bRecheckNoRealToRatReverseCastStatus where
  | noRealToRatReverseCast
  deriving DecidableEq, Repr

inductive SM6bRecheckNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM6bRecheckNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM6bRecheckNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM6bRecheckNoNewInverseOracleStatus where
  | noNewInverseOracle
  deriving DecidableEq, Repr

inductive SM6bRecheckNoProductIdentityProofStatus where
  | noProductIdentityProof
  deriving DecidableEq, Repr

inductive SM6bRecheckNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM6bRecheckNoNewInteriorEliminationCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM6bRecheckNoDtnMultiSchurRecomputationStatus where
  | noDtnGeneralizedDtnOrMultiSchurRecomputation
  deriving DecidableEq, Repr

inductive SM6bRecheckNoLevelHistoryMatrixStatus where
  | noLevelHistoryMatrix
  deriving DecidableEq, Repr

inductive SM6bRecheckNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantOrHeegner
  deriving DecidableEq, Repr

structure GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
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
  sourceSM6b : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G
  sourceSM5qRecheck :
    GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G
  sourceSM5qRecheck_source_eq_SM6_source :
    sourceSM5qRecheck.sourceSM5 = sourceSM6b.sourceSM6Witness.source
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM6b : boundaryOperatorReal = sourceSM6b.boundaryOperatorReal
  execBoundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  execBoundaryOperator_eq_SM5qRecheck : execBoundaryOperator = sourceSM5qRecheck.execBoundaryOperator
  execBoundaryOperator_bridge_to_SM6 : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      ((sourceSM6b.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ)
  execBoundaryOperator_bridge_to_SM6bReal : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      ((sourceSM6b.boundaryOperatorReal i j : ℝ) : ℂ)
  entry_eq_SM5 : ∀ i j,
    boundaryOperatorReal i j = sourceSM6b.sourceSM6Witness.source.boundaryOperator i j
  entry_eq_SM5qRecheck : ∀ i j,
    boundaryOperatorReal i j = sourceSM5qRecheck.sourceSM5.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM6b.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  apply_eq_SM5 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM6b.sourceSM6Witness.«apply» φ = sourceSM6b.sourceSM6Witness.source.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM6b.sourceSM6Witness.«apply» φ = boundaryOperatorReal.mulVec φ
  completionStatus : SM6bRecheckCompletionStatus
  completionStatus_eq :
    completionStatus = SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck
  nextPhaseStatus : SM6bRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM6bRecheckNextPhaseStatus.sm8MayConsumeLevelStepExecMirror
  noFreeExecMatrixStatus : SM6bRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM6bRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatReverseCastStatus : SM6bRecheckNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM6bRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM6bRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM6bRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM6bRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM6bRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM6bRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM6bRecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM6bRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM6bRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityProofStatus : SM6bRecheckNoProductIdentityProofStatus
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus = SM6bRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noTwoSidedInvStatus : SM6bRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM6bRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewInteriorEliminationCertificateStatus : SM6bRecheckNoNewInteriorEliminationCertificateStatus
  noNewInteriorEliminationCertificateStatus_eq :
    noNewInteriorEliminationCertificateStatus =
      SM6bRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM6bRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM6bRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noLevelHistoryMatrixStatus : SM6bRecheckNoLevelHistoryMatrixStatus
  noLevelHistoryMatrixStatus_eq :
    noLevelHistoryMatrixStatus = SM6bRecheckNoLevelHistoryMatrixStatus.noLevelHistoryMatrix
  noCharpolyDiscriminantHeegnerStatus : SM6bRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM6bRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

namespace GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b

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
    (B : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G)
    (Q : GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q Cell p A P wp W E K T M S H G)
    (hQ : Q.sourceSM5 = B.sourceSM6Witness.source) :
    GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G where
  sourceSM6b := B
  sourceSM5qRecheck := Q
  sourceSM5qRecheck_source_eq_SM6_source := hQ
  boundaryOperatorReal := B.boundaryOperatorReal
  boundaryOperatorReal_eq_SM6b := by
    rfl
  execBoundaryOperator := Q.execBoundaryOperator
  execBoundaryOperator_eq_SM5qRecheck := by
    rfl
  execBoundaryOperator_bridge_to_SM6 := by
    intro i j
    calc
      ExecComplexBridge.toComplex (Q.execBoundaryOperator i j) =
          ((Q.sourceSM5.boundaryOperator i j : ℝ) : ℂ) :=
        Q.execBoundaryOperator_bridge_to_SM5 i j
      _ = ((B.sourceSM6Witness.source.boundaryOperator i j : ℝ) : ℂ) := by
        rw [hQ]
      _ = ((B.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ) := by
        rw [← B.sourceSM6Witness.boundaryOperator_eq_SM5]
  execBoundaryOperator_bridge_to_SM6bReal := by
    intro i j
    calc
      ExecComplexBridge.toComplex (Q.execBoundaryOperator i j) =
          ((B.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ) := by
        calc
          ExecComplexBridge.toComplex (Q.execBoundaryOperator i j) =
              ((Q.sourceSM5.boundaryOperator i j : ℝ) : ℂ) :=
            Q.execBoundaryOperator_bridge_to_SM5 i j
          _ = ((B.sourceSM6Witness.source.boundaryOperator i j : ℝ) : ℂ) := by
            rw [hQ]
          _ = ((B.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ) := by
            rw [← B.sourceSM6Witness.boundaryOperator_eq_SM5]
      _ = ((B.boundaryOperatorReal i j : ℝ) : ℂ) := by
        rw [← B.boundaryOperatorReal_eq_SM6]
  entry_eq_SM5 := by
    intro i j
    exact B.entry_eq_SM5 i j
  entry_eq_SM5qRecheck := by
    intro i j
    calc
      B.boundaryOperatorReal i j = B.sourceSM6Witness.source.boundaryOperator i j :=
        B.entry_eq_SM5 i j
      _ = Q.sourceSM5.boundaryOperator i j := by
        rw [← hQ]
  entry_eq_schur := by
    intro i j
    exact B.entry_eq_schur i j
  apply_eq_SM5 := by
    intro φ
    exact B.apply_eq_SM5 φ
  apply_eq_mulVec := by
    intro φ
    exact B.apply_eq_mulVec φ
  completionStatus := SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck
  completionStatus_eq := by
    rfl
  nextPhaseStatus := SM6bRecheckNextPhaseStatus.sm8MayConsumeLevelStepExecMirror
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM6bRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM6bRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM6bRecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM6bRecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM6bRecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM6bRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus := SM6bRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM6bRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewInteriorEliminationCertificateStatus :=
    SM6bRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noNewInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM6bRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noLevelHistoryMatrixStatus := SM6bRecheckNoLevelHistoryMatrixStatus.noLevelHistoryMatrix
  noLevelHistoryMatrixStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM6bRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem sourceSM5qRecheck_source_from_SM6
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G) :
    X.sourceSM5qRecheck.sourceSM5 = X.sourceSM6b.sourceSM6Witness.source :=
  X.sourceSM5qRecheck_source_eq_SM6_source

theorem execBoundaryOperator_from_SM5qRecheck
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G) :
    X.execBoundaryOperator = X.sourceSM5qRecheck.execBoundaryOperator :=
  X.execBoundaryOperator_eq_SM5qRecheck

theorem execBoundaryOperator_bridge_to_SM6_thm
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (X.execBoundaryOperator i j) =
      ((X.sourceSM6b.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ) :=
  X.execBoundaryOperator_bridge_to_SM6 i j

theorem execBoundaryOperator_bridge_to_SM6bReal_thm
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (X.execBoundaryOperator i j) =
      ((X.sourceSM6b.boundaryOperatorReal i j : ℝ) : ℂ) :=
  X.execBoundaryOperator_bridge_to_SM6bReal i j

theorem entryReal_from_SM5qRecheck
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM5qRecheck.sourceSM5.boundaryOperator i j :=
  X.entry_eq_SM5qRecheck i j

theorem entryReal_from_SM6b_SM5
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM6b.sourceSM6Witness.source.boundaryOperator i j :=
  X.entry_eq_SM5 i j

theorem entryReal_from_schur
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          X.sourceSM6b.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j :=
  X.entry_eq_schur i j

theorem apply_from_SM5
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM6b.sourceSM6Witness.«apply» φ = X.sourceSM6b.sourceSM6Witness.source.«apply» φ :=
  X.apply_eq_SM5 φ

theorem apply_from_boundaryOperatorReal_mulVec
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM6b.sourceSM6Witness.«apply» φ = X.boundaryOperatorReal.mulVec φ :=
  X.apply_eq_mulVec φ

theorem completion_closed_from_SM5qRecheck
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G) :
    X.completionStatus = SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck :=
  X.completionStatus_eq

theorem next_phase_is_SM8
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G) :
    X.nextPhaseStatus = SM6bRecheckNextPhaseStatus.sm8MayConsumeLevelStepExecMirror :=
  X.nextPhaseStatus_eq

theorem no_forbidden_shortcuts
    (X : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G) :
    X.noFreeExecMatrixStatus = SM6bRecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    X.noRealToRatReverseCastStatus = SM6bRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast ∧
    X.noScalarInverseStatus = SM6bRecheckNoScalarInverseStatus.noScalarInverse ∧
    X.noMatrixInvStatus = SM6bRecheckNoMatrixInvStatus.noMatrixInv ∧
    X.noFieldSimpStatus = SM6bRecheckNoFieldSimpStatus.noFieldSimp ∧
    X.noNewInverseOracleStatus = SM6bRecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    X.noProductIdentityProofStatus = SM6bRecheckNoProductIdentityProofStatus.noProductIdentityProof ∧
    X.noTwoSidedInvStatus = SM6bRecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    X.noNewInteriorEliminationCertificateStatus =
      SM6bRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate ∧
    X.noDtnMultiSchurRecomputationStatus =
      SM6bRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation ∧
    X.noLevelHistoryMatrixStatus = SM6bRecheckNoLevelHistoryMatrixStatus.noLevelHistoryMatrix ∧
    X.noCharpolyDiscriminantHeegnerStatus =
      SM6bRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
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
   X.noLevelHistoryMatrixStatus_eq,
   X.noCharpolyDiscriminantHeegnerStatus_eq⟩

end GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b

def regularGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
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
  GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b.fromSources
    (regularGeneratedLevelStepExecMirrorSourceSM6b
      (sm6GeneratedLevelStepWitnessLedger_from_accumulatedEntryCancellationLedger L level levelIndex))
    (regularGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L)
    (by rfl)

def variableGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
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
  GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b.fromSources
    (variableGeneratedLevelStepExecMirrorSourceSM6b
      (sm6GeneratedLevelStepWitnessLedger_from_accumulatedEntryCancellationLedger L level levelIndex))
    (variableGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q L)
    (by rfl)

structure SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM5qRecheckLedger :
    SM5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger
      b β p regularWeight variableWeight
  sourceSM6bLedger : SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM6bLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableSource :
    GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM6bLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularExecBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularSource.execBoundaryOperator i j) =
      ((regularSource.sourceSM6b.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ)
  variableExecBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableSource.execBoundaryOperator i j) =
      ((variableSource.sourceSM6b.sourceSM6Witness.boundaryOperator i j : ℝ) : ℂ)
  regularSourceSM5qRecheck_eq_SM6Source :
    regularSource.sourceSM5qRecheck.sourceSM5 = regularSource.sourceSM6b.sourceSM6Witness.source
  variableSourceSM5qRecheck_eq_SM6Source :
    variableSource.sourceSM5qRecheck.sourceSM5 = variableSource.sourceSM6b.sourceSM6Witness.source
  regularCompletionStatus : SM6bRecheckCompletionStatus
  regularCompletionStatus_eq :
    regularCompletionStatus = SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck
  variableCompletionStatus : SM6bRecheckCompletionStatus
  variableCompletionStatus_eq :
    variableCompletionStatus = SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck
  nextPhaseStatus : SM6bRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM6bRecheckNextPhaseStatus.sm8MayConsumeLevelStepExecMirror
  noFreeExecMatrixStatus : SM6bRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM6bRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatReverseCastStatus : SM6bRecheckNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM6bRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM6bRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM6bRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM6bRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM6bRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM6bRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM6bRecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM6bRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM6bRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityProofStatus : SM6bRecheckNoProductIdentityProofStatus
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus = SM6bRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noTwoSidedInvStatus : SM6bRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM6bRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewInteriorEliminationCertificateStatus : SM6bRecheckNoNewInteriorEliminationCertificateStatus
  noNewInteriorEliminationCertificateStatus_eq :
    noNewInteriorEliminationCertificateStatus =
      SM6bRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM6bRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM6bRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noLevelHistoryMatrixStatus : SM6bRecheckNoLevelHistoryMatrixStatus
  noLevelHistoryMatrixStatus_eq :
    noLevelHistoryMatrixStatus = SM6bRecheckNoLevelHistoryMatrixStatus.noLevelHistoryMatrix
  noCharpolyDiscriminantHeegnerStatus : SM6bRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM6bRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

def sm6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
      b β p regularWeight variableWeight where
  sourceSM5qRecheckLedger :=
    sm5qRecheckGeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckLedger L
  sourceSM6bLedger :=
    sm6bGeneratedLevelStepExecMirrorSourceLedger
      (sm6GeneratedLevelStepWitnessLedger_from_accumulatedEntryCancellationLedger L level levelIndex)
  regularSource := regularGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex
  variableSource := variableGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex
  regularExecBoundaryOperatorBridge := by
    intro i j
    exact (regularGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex).execBoundaryOperator_bridge_to_SM6 i j
  variableExecBoundaryOperatorBridge := by
    intro i j
    exact (variableGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex).execBoundaryOperator_bridge_to_SM6 i j
  regularSourceSM5qRecheck_eq_SM6Source := by
    exact (regularGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex).sourceSM5qRecheck_source_eq_SM6_source
  variableSourceSM5qRecheck_eq_SM6Source := by
    exact (variableGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex).sourceSM5qRecheck_source_eq_SM6_source
  regularCompletionStatus := SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck
  regularCompletionStatus_eq := by
    rfl
  variableCompletionStatus := SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck
  variableCompletionStatus_eq := by
    rfl
  nextPhaseStatus := SM6bRecheckNextPhaseStatus.sm8MayConsumeLevelStepExecMirror
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM6bRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM6bRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM6bRecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM6bRecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM6bRecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM6bRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus := SM6bRecheckNoProductIdentityProofStatus.noProductIdentityProof
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM6bRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewInteriorEliminationCertificateStatus :=
    SM6bRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noNewInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM6bRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noLevelHistoryMatrixStatus := SM6bRecheckNoLevelHistoryMatrixStatus.noLevelHistoryMatrix
  noLevelHistoryMatrixStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM6bRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem sm6bRecheck_regularCompletion_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
      b β p regularWeight variableWeight) :
    L.regularCompletionStatus = SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck :=
  L.regularCompletionStatus_eq

theorem sm6bRecheck_variableCompletion_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
      b β p regularWeight variableWeight) :
    L.variableCompletionStatus = SM6bRecheckCompletionStatus.execMirrorCompletedFromSM5qRecheck :=
  L.variableCompletionStatus_eq

theorem sm6bRecheck_nextPhase_is_SM8
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
      b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM6bRecheckNextPhaseStatus.sm8MayConsumeLevelStepExecMirror :=
  L.nextPhaseStatus_eq

theorem sm6bRecheck_noForbiddenShortcuts
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
      b β p regularWeight variableWeight) :
    L.noFreeExecMatrixStatus = SM6bRecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    L.noRealToRatReverseCastStatus = SM6bRecheckNoRealToRatReverseCastStatus.noRealToRatReverseCast ∧
    L.noScalarInverseStatus = SM6bRecheckNoScalarInverseStatus.noScalarInverse ∧
    L.noMatrixInvStatus = SM6bRecheckNoMatrixInvStatus.noMatrixInv ∧
    L.noFieldSimpStatus = SM6bRecheckNoFieldSimpStatus.noFieldSimp ∧
    L.noNewInverseOracleStatus = SM6bRecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    L.noProductIdentityProofStatus = SM6bRecheckNoProductIdentityProofStatus.noProductIdentityProof ∧
    L.noTwoSidedInvStatus = SM6bRecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    L.noNewInteriorEliminationCertificateStatus =
      SM6bRecheckNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate ∧
    L.noDtnMultiSchurRecomputationStatus =
      SM6bRecheckNoDtnMultiSchurRecomputationStatus.noDtnGeneralizedDtnOrMultiSchurRecomputation ∧
    L.noLevelHistoryMatrixStatus = SM6bRecheckNoLevelHistoryMatrixStatus.noLevelHistoryMatrix ∧
    L.noCharpolyDiscriminantHeegnerStatus =
      SM6bRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
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
   L.noLevelHistoryMatrixStatus_eq,
   L.noCharpolyDiscriminantHeegnerStatus_eq⟩

end Smoke

end CNNA.PillarA.Arithmetic
