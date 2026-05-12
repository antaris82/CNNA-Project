import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8
import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM8RecheckCompletionStatus where
  | completedFromSM6bRecheck
  deriving DecidableEq, Repr

inductive SM8RecheckNoFreeExecMatrixStatus where
  | noFreeExecMatrix
  deriving DecidableEq, Repr

inductive SM8RecheckNoRealToRatConversionStatus where
  | noRealToRatConversion
  deriving DecidableEq, Repr

inductive SM8RecheckNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM8RecheckNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM8RecheckNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM8RecheckNoNewInverseOracleStatus where
  | noNewInverseOracle
  deriving DecidableEq, Repr

inductive SM8RecheckNoProductIdentityStatus where
  | noProductIdentity
  deriving DecidableEq, Repr

inductive SM8RecheckNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM8RecheckNoNewCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM8RecheckNoDtnMultiSchurRecomputationStatus where
  | noDtnMultiSchurRecomputation
  deriving DecidableEq, Repr

inductive SM8RecheckNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantHeegner
  deriving DecidableEq, Repr

inductive SM8RecheckNextPhaseStatus where
  | sm9aRecheckMayConsumeSM8ExecMatrix
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

abbrev GeneratedLevelHistoryExecMatrixIndexSM8Recheck
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G) :=
  GeneratedLevelHistoryMatrixIndexSM8 X.sourceBridge

def generatedLevelHistoryExecMatrixFromSM6bRecheckSM8
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G)
    (Y : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
      Cell p A P wp W E K T M S H G) :
    Matrix (GeneratedLevelHistoryExecMatrixIndexSM8Recheck X)
      (GeneratedLevelHistoryExecMatrixIndexSM8Recheck X) ExecComplex :=
  fun i j =>
    Y.execBoundaryOperator (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j)

theorem generatedLevelHistoryExecMatrixFromSM6bRecheckSM8_apply
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G)
    (Y : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
      Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck X) :
    generatedLevelHistoryExecMatrixFromSM6bRecheckSM8 X Y i j =
      Y.execBoundaryOperator (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j) := by
  rfl

structure GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
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
  sourceSM8 : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G
  sourceSM6bRecheck :
    GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b Cell p A P wp W E K T M S H G
  sourceSM6bRecheck_witness_eq_SM8_witness :
    sourceSM6bRecheck.sourceSM6b.sourceSM6Witness = sourceSM8.sourceBridge.sourceSM6Witness
  matrixReal : Matrix (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8)
    (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8) ℝ
  matrixReal_eq_SM8 : matrixReal = sourceSM8.matrix
  execMatrix : Matrix (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8)
    (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8) ExecComplex
  execMatrix_eq_pullback :
    execMatrix = generatedLevelHistoryExecMatrixFromSM6bRecheckSM8 sourceSM8 sourceSM6bRecheck
  execMatrix_bridge_to_SM8 : ∀ i j,
    ExecComplexBridge.toComplex (execMatrix i j) = (sourceSM8.matrix i j : ℂ)
  entryReal_eq_SM8 : ∀ i j, matrixReal i j = sourceSM8.matrix i j
  entryReal_eq_boundaryOperator : ∀ i j,
    matrixReal i j =
      sourceSM8.sourceBridge.sourceSM6Witness.boundaryOperator
        (sourceSM8.sourceBridge.toBoundaryIndex i) (sourceSM8.sourceBridge.toBoundaryIndex j)
  entryReal_eq_SM6 : ∀ i j,
    matrixReal i j =
      sourceSM8.sourceBridge.sourceSM6Witness.source.boundaryOperator
        (sourceSM8.sourceBridge.toBoundaryIndex i) (sourceSM8.sourceBridge.toBoundaryIndex j)
  entryReal_eq_schur : ∀ i j,
    matrixReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM8.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (sourceSM8.sourceBridge.toBoundaryIndex i) (sourceSM8.sourceBridge.toBoundaryIndex j)
  execEntry_from_SM6bRecheck : ∀ i j,
    execMatrix i j =
      sourceSM6bRecheck.execBoundaryOperator
        (sourceSM8.sourceBridge.toBoundaryIndex i) (sourceSM8.sourceBridge.toBoundaryIndex j)
  completionStatus : SM8RecheckCompletionStatus
  completionStatus_eq : completionStatus = SM8RecheckCompletionStatus.completedFromSM6bRecheck
  noFreeExecMatrixStatus : SM8RecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM8RecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatConversionStatus : SM8RecheckNoRealToRatConversionStatus
  noRealToRatConversionStatus_eq :
    noRealToRatConversionStatus = SM8RecheckNoRealToRatConversionStatus.noRealToRatConversion
  noScalarInverseStatus : SM8RecheckNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM8RecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM8RecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM8RecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM8RecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM8RecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM8RecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM8RecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityStatus : SM8RecheckNoProductIdentityStatus
  noProductIdentityStatus_eq :
    noProductIdentityStatus = SM8RecheckNoProductIdentityStatus.noProductIdentity
  noTwoSidedInvStatus : SM8RecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM8RecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewCertificateStatus : SM8RecheckNoNewCertificateStatus
  noNewCertificateStatus_eq :
    noNewCertificateStatus = SM8RecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM8RecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM8RecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM8RecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM8RecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner
  nextPhaseStatus : SM8RecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM8RecheckNextPhaseStatus.sm9aRecheckMayConsumeSM8ExecMatrix

namespace GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8

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
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G)
    (Y : GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b
      Cell p A P wp W E K T M S H G)
    (h : Y.sourceSM6b.sourceSM6Witness = X.sourceBridge.sourceSM6Witness) :
    GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G where
  sourceSM8 := X
  sourceSM6bRecheck := Y
  sourceSM6bRecheck_witness_eq_SM8_witness := h
  matrixReal := X.matrix
  matrixReal_eq_SM8 := by
    rfl
  execMatrix := generatedLevelHistoryExecMatrixFromSM6bRecheckSM8 X Y
  execMatrix_eq_pullback := by
    rfl
  execMatrix_bridge_to_SM8 := by
    intro i j
    calc
      ExecComplexBridge.toComplex
          (generatedLevelHistoryExecMatrixFromSM6bRecheckSM8 X Y i j) =
          ((Y.sourceSM6b.sourceSM6Witness.boundaryOperator
            (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j) : ℝ) : ℂ) :=
        Y.execBoundaryOperator_bridge_to_SM6
          (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j)
      _ = ((X.sourceBridge.sourceSM6Witness.boundaryOperator
            (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j) : ℝ) : ℂ) := by
        rw [h]
      _ = (X.matrix i j : ℂ) := by
        rw [← X.entry_eq_boundaryOperator i j]
  entryReal_eq_SM8 := by
    intro i j
    rfl
  entryReal_eq_boundaryOperator := by
    intro i j
    exact X.entry_eq_boundaryOperator i j
  entryReal_eq_SM6 := by
    intro i j
    exact X.entry_eq_SM6 i j
  entryReal_eq_schur := by
    intro i j
    exact X.entry_eq_schur i j
  execEntry_from_SM6bRecheck := by
    intro i j
    rfl
  completionStatus := SM8RecheckCompletionStatus.completedFromSM6bRecheck
  completionStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM8RecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatConversionStatus := SM8RecheckNoRealToRatConversionStatus.noRealToRatConversion
  noRealToRatConversionStatus_eq := by
    rfl
  noScalarInverseStatus := SM8RecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM8RecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM8RecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM8RecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityStatus := SM8RecheckNoProductIdentityStatus.noProductIdentity
  noProductIdentityStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM8RecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewCertificateStatus := SM8RecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noNewCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM8RecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM8RecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl
  nextPhaseStatus := SM8RecheckNextPhaseStatus.sm9aRecheckMayConsumeSM8ExecMatrix
  nextPhaseStatus_eq := by
    rfl

theorem execMatrix_bridge_to_SM8_thm
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8) :
    ExecComplexBridge.toComplex (Z.execMatrix i j) = (Z.sourceSM8.matrix i j : ℂ) :=
  Z.execMatrix_bridge_to_SM8 i j

theorem execEntry_from_SM6bRecheck_thm
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8) :
    Z.execMatrix i j =
      Z.sourceSM6bRecheck.execBoundaryOperator
        (Z.sourceSM8.sourceBridge.toBoundaryIndex i) (Z.sourceSM8.sourceBridge.toBoundaryIndex j) :=
  Z.execEntry_from_SM6bRecheck i j

theorem entryReal_from_SM8
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8) :
    Z.matrixReal i j = Z.sourceSM8.matrix i j :=
  Z.entryReal_eq_SM8 i j

theorem entryReal_from_schur
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8) :
    Z.matrixReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          Z.sourceSM8.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (Z.sourceSM8.sourceBridge.toBoundaryIndex i) (Z.sourceSM8.sourceBridge.toBoundaryIndex j) :=
  Z.entryReal_eq_schur i j

theorem completed_from_SM6bRecheck
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G) :
    Z.completionStatus = SM8RecheckCompletionStatus.completedFromSM6bRecheck :=
  Z.completionStatus_eq

theorem no_forbidden_shortcuts
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G) :
    Z.noFreeExecMatrixStatus = SM8RecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    Z.noRealToRatConversionStatus = SM8RecheckNoRealToRatConversionStatus.noRealToRatConversion ∧
    Z.noScalarInverseStatus = SM8RecheckNoScalarInverseStatus.noScalarInverse ∧
    Z.noMatrixInvStatus = SM8RecheckNoMatrixInvStatus.noMatrixInv ∧
    Z.noFieldSimpStatus = SM8RecheckNoFieldSimpStatus.noFieldSimp ∧
    Z.noNewInverseOracleStatus = SM8RecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    Z.noProductIdentityStatus = SM8RecheckNoProductIdentityStatus.noProductIdentity ∧
    Z.noTwoSidedInvStatus = SM8RecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    Z.noNewCertificateStatus = SM8RecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate ∧
    Z.noDtnMultiSchurRecomputationStatus =
      SM8RecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation ∧
    Z.noCharpolyDiscriminantHeegnerStatus =
      SM8RecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner :=
  ⟨Z.noFreeExecMatrixStatus_eq,
   Z.noRealToRatConversionStatus_eq,
   Z.noScalarInverseStatus_eq,
   Z.noMatrixInvStatus_eq,
   Z.noFieldSimpStatus_eq,
   Z.noNewInverseOracleStatus_eq,
   Z.noProductIdentityStatus_eq,
   Z.noTwoSidedInvStatus_eq,
   Z.noNewCertificateStatus_eq,
   Z.noDtnMultiSchurRecomputationStatus_eq,
   Z.noCharpolyDiscriminantHeegnerStatus_eq⟩

end GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8

def regularGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
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
  GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8.fromSources
    (regularGeneratedLevelHistoryMatrixFromBridgeSM8
      (sm7BridgeRecheckLedger_from_SM5
        (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L) level levelIndex))
    (regularGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex)
    (by rfl)

def variableGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
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
  GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8.fromSources
    (variableGeneratedLevelHistoryMatrixFromBridgeSM8
      (sm7BridgeRecheckLedger_from_SM5
        (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L) level levelIndex))
    (variableGeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b L level levelIndex)
    (by rfl)

structure SM8RecheckGeneratedLevelHistoryExecMatrixLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM8Ledger : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight
  sourceSM6bRecheckLedger :
    SM6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger
      b β p regularWeight variableWeight
  regularExecMatrix :
    GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableExecMatrix :
    GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularExecMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularExecMatrix.execMatrix i j) =
      (regularExecMatrix.sourceSM8.matrix i j : ℂ)
  variableExecMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableExecMatrix.execMatrix i j) =
      (variableExecMatrix.sourceSM8.matrix i j : ℂ)
  regularExecEntry_from_SM6bRecheck : ∀ i j,
    regularExecMatrix.execMatrix i j =
      regularExecMatrix.sourceSM6bRecheck.execBoundaryOperator
        (regularExecMatrix.sourceSM8.sourceBridge.toBoundaryIndex i)
        (regularExecMatrix.sourceSM8.sourceBridge.toBoundaryIndex j)
  variableExecEntry_from_SM6bRecheck : ∀ i j,
    variableExecMatrix.execMatrix i j =
      variableExecMatrix.sourceSM6bRecheck.execBoundaryOperator
        (variableExecMatrix.sourceSM8.sourceBridge.toBoundaryIndex i)
        (variableExecMatrix.sourceSM8.sourceBridge.toBoundaryIndex j)
  completionStatus : SM8RecheckCompletionStatus
  completionStatus_eq : completionStatus = SM8RecheckCompletionStatus.completedFromSM6bRecheck
  nextPhaseStatus : SM8RecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM8RecheckNextPhaseStatus.sm9aRecheckMayConsumeSM8ExecMatrix
  noFreeExecMatrixStatus : SM8RecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM8RecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatConversionStatus : SM8RecheckNoRealToRatConversionStatus
  noRealToRatConversionStatus_eq :
    noRealToRatConversionStatus = SM8RecheckNoRealToRatConversionStatus.noRealToRatConversion
  noScalarInverseStatus : SM8RecheckNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM8RecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM8RecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM8RecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM8RecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM8RecheckNoFieldSimpStatus.noFieldSimp
  noNewInverseOracleStatus : SM8RecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM8RecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityStatus : SM8RecheckNoProductIdentityStatus
  noProductIdentityStatus_eq :
    noProductIdentityStatus = SM8RecheckNoProductIdentityStatus.noProductIdentity
  noTwoSidedInvStatus : SM8RecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM8RecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewCertificateStatus : SM8RecheckNoNewCertificateStatus
  noNewCertificateStatus_eq :
    noNewCertificateStatus = SM8RecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM8RecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM8RecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM8RecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM8RecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner

def sm8RecheckGeneratedLevelHistoryExecMatrixLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight where
  sourceSM8Ledger :=
    sm8GeneratedLevelHistoryMatrixLedger_from_SM5
      (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L) level levelIndex
  sourceSM6bRecheckLedger :=
    sm6bRecheckGeneratedLevelStepExecMirrorSourceFromSM5qRecheckLedger L level levelIndex
  regularExecMatrix := regularGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 L level levelIndex
  variableExecMatrix := variableGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 L level levelIndex
  regularExecMatrixBridge := by
    intro i j
    exact (regularGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 L level levelIndex).execMatrix_bridge_to_SM8 i j
  variableExecMatrixBridge := by
    intro i j
    exact (variableGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 L level levelIndex).execMatrix_bridge_to_SM8 i j
  regularExecEntry_from_SM6bRecheck := by
    intro i j
    exact (regularGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 L level levelIndex).execEntry_from_SM6bRecheck i j
  variableExecEntry_from_SM6bRecheck := by
    intro i j
    exact (variableGeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 L level levelIndex).execEntry_from_SM6bRecheck i j
  completionStatus := SM8RecheckCompletionStatus.completedFromSM6bRecheck
  completionStatus_eq := by
    rfl
  nextPhaseStatus := SM8RecheckNextPhaseStatus.sm9aRecheckMayConsumeSM8ExecMatrix
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM8RecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatConversionStatus := SM8RecheckNoRealToRatConversionStatus.noRealToRatConversion
  noRealToRatConversionStatus_eq := by
    rfl
  noScalarInverseStatus := SM8RecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM8RecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM8RecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM8RecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityStatus := SM8RecheckNoProductIdentityStatus.noProductIdentity
  noProductIdentityStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM8RecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewCertificateStatus := SM8RecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noNewCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM8RecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM8RecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem sm8Recheck_regularExecMatrix_bridge
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck L.regularExecMatrix.sourceSM8) :
    ExecComplexBridge.toComplex (L.regularExecMatrix.execMatrix i j) =
      (L.regularExecMatrix.sourceSM8.matrix i j : ℂ) :=
  L.regularExecMatrixBridge i j

theorem sm8Recheck_variableExecMatrix_bridge
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck L.variableExecMatrix.sourceSM8) :
    ExecComplexBridge.toComplex (L.variableExecMatrix.execMatrix i j) =
      (L.variableExecMatrix.sourceSM8.matrix i j : ℂ) :=
  L.variableExecMatrixBridge i j

theorem sm8Recheck_completed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    L.completionStatus = SM8RecheckCompletionStatus.completedFromSM6bRecheck :=
  L.completionStatus_eq

theorem sm8Recheck_nextPhase_SM9aRecheck
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM8RecheckNextPhaseStatus.sm9aRecheckMayConsumeSM8ExecMatrix :=
  L.nextPhaseStatus_eq

theorem sm8Recheck_noMatrixInv
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    L.noMatrixInvStatus = SM8RecheckNoMatrixInvStatus.noMatrixInv :=
  L.noMatrixInvStatus_eq

theorem sm8Recheck_noCharpolyDiscriminantHeegner
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    L.noCharpolyDiscriminantHeegnerStatus =
      SM8RecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner :=
  L.noCharpolyDiscriminantHeegnerStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
