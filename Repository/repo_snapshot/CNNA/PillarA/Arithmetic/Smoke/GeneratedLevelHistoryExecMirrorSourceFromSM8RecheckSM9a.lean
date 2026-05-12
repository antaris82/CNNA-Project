import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a
import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM9aRecheckCompletionStatus where
  | missingExecMirrorSourceClosedFromSM8Recheck
  deriving DecidableEq, Repr

inductive SM9aRecheckNextPhaseStatus where
  | sm9bMayConsumeComputedExecMirror
  deriving DecidableEq, Repr

inductive SM9aRecheckNoFreeExecMatrixStatus where
  | noFreeExecMatrix
  deriving DecidableEq, Repr

inductive SM9aRecheckNoRealToRatConversionStatus where
  | noRealToRatConversion
  deriving DecidableEq, Repr

inductive SM9aRecheckNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM9aRecheckNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9aRecheckNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9aRecheckNoTestMatrixStatus where
  | noTestMatrix
  deriving DecidableEq, Repr

inductive SM9aRecheckNoNewInverseOracleStatus where
  | noNewInverseOracle
  deriving DecidableEq, Repr

inductive SM9aRecheckNoProductIdentityStatus where
  | noProductIdentity
  deriving DecidableEq, Repr

inductive SM9aRecheckNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM9aRecheckNoNewCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM9aRecheckNoDtnMultiSchurRecomputationStatus where
  | noDtnMultiSchurRecomputation
  deriving DecidableEq, Repr

inductive SM9aRecheckNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantHeegner
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

structure GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
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
  sourceSM8Recheck :
    GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G
  sourceSM9a : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G
  sourceSM9a_eq_from_SM8Recheck :
    sourceSM9a = GeneratedLevelHistoryExecMirrorSourceSM9a.fromSM8 sourceSM8Recheck.sourceSM8
  sourceSM8Recheck_source_eq_SM9a_source :
    sourceSM8Recheck.sourceSM8 = sourceSM9a.sourceSM8Matrix
  execMatrix : Matrix (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8Recheck.sourceSM8)
    (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8Recheck.sourceSM8) ExecComplex
  execMatrix_eq_SM8Recheck : execMatrix = sourceSM8Recheck.execMatrix
  entryReal : Matrix (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8Recheck.sourceSM8)
    (GeneratedLevelHistoryExecMatrixIndexSM8Recheck sourceSM8Recheck.sourceSM8) ℝ
  entryReal_eq_SM8Recheck : entryReal = sourceSM8Recheck.matrixReal
  entryReal_eq_SM9aFromSM8Recheck : ∀ i j,
    entryReal i j =
      (GeneratedLevelHistoryExecMirrorSourceSM9a.fromSM8 sourceSM8Recheck.sourceSM8).entryReal i j
  execMatrix_bridge_to_SM9a : ∀ i j,
    ExecComplexBridge.toComplex (execMatrix i j) = (entryReal i j : ℂ)
  execMatrix_bridge_to_SM8 : ∀ i j,
    ExecComplexBridge.toComplex (execMatrix i j) = (sourceSM8Recheck.sourceSM8.matrix i j : ℂ)
  execMatrix_bridge_to_SM8Recheck : ∀ i j,
    ExecComplexBridge.toComplex (execMatrix i j) = (sourceSM8Recheck.matrixReal i j : ℂ)
  entryReal_eq_SM8 : ∀ i j, entryReal i j = sourceSM8Recheck.sourceSM8.matrix i j
  entryReal_eq_generatedLevelHistoryMatrix : ∀ i j,
    entryReal i j = generatedLevelHistoryMatrixSM8 sourceSM8Recheck.sourceSM8.sourceBridge i j
  entryReal_eq_boundaryOperator : ∀ i j,
    entryReal i j =
      sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.boundaryOperator
        (sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j)
  entryReal_eq_SM6 : ∀ i j,
    entryReal i j =
      sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.source.boundaryOperator
        (sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j)
  entryReal_eq_schur : ∀ i j,
    entryReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j)
  execEntry_from_SM8Recheck : ∀ i j,
    execMatrix i j = sourceSM8Recheck.execMatrix i j
  completionStatus : SM9aRecheckCompletionStatus
  completionStatus_eq :
    completionStatus = SM9aRecheckCompletionStatus.missingExecMirrorSourceClosedFromSM8Recheck
  nextPhaseStatus : SM9aRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9aRecheckNextPhaseStatus.sm9bMayConsumeComputedExecMirror
  noFreeExecMatrixStatus : SM9aRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM9aRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatConversionStatus : SM9aRecheckNoRealToRatConversionStatus
  noRealToRatConversionStatus_eq :
    noRealToRatConversionStatus = SM9aRecheckNoRealToRatConversionStatus.noRealToRatConversion
  noScalarInverseStatus : SM9aRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM9aRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM9aRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9aRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9aRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9aRecheckNoFieldSimpStatus.noFieldSimp
  noTestMatrixStatus : SM9aRecheckNoTestMatrixStatus
  noTestMatrixStatus_eq : noTestMatrixStatus = SM9aRecheckNoTestMatrixStatus.noTestMatrix
  noNewInverseOracleStatus : SM9aRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM9aRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityStatus : SM9aRecheckNoProductIdentityStatus
  noProductIdentityStatus_eq :
    noProductIdentityStatus = SM9aRecheckNoProductIdentityStatus.noProductIdentity
  noTwoSidedInvStatus : SM9aRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM9aRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewCertificateStatus : SM9aRecheckNoNewCertificateStatus
  noNewCertificateStatus_eq :
    noNewCertificateStatus = SM9aRecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM9aRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM9aRecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM9aRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM9aRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner

namespace GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a

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

def fromSM8Recheck
    (Z : GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8 Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G where
  sourceSM8Recheck := Z
  sourceSM9a := GeneratedLevelHistoryExecMirrorSourceSM9a.fromSM8 Z.sourceSM8
  sourceSM9a_eq_from_SM8Recheck := by
    rfl
  sourceSM8Recheck_source_eq_SM9a_source := by
    rfl
  execMatrix := Z.execMatrix
  execMatrix_eq_SM8Recheck := by
    rfl
  entryReal := Z.matrixReal
  entryReal_eq_SM8Recheck := by
    rfl
  entryReal_eq_SM9aFromSM8Recheck := by
    intro i j
    exact Z.entryReal_eq_SM8 i j
  execMatrix_bridge_to_SM9a := by
    intro i j
    calc
      ExecComplexBridge.toComplex (Z.execMatrix i j) = (Z.sourceSM8.matrix i j : ℂ) :=
        Z.execMatrix_bridge_to_SM8 i j
      _ = (Z.matrixReal i j : ℂ) := by
        rw [← Z.entryReal_eq_SM8 i j]
  execMatrix_bridge_to_SM8 := by
    intro i j
    exact Z.execMatrix_bridge_to_SM8 i j
  execMatrix_bridge_to_SM8Recheck := by
    intro i j
    calc
      ExecComplexBridge.toComplex (Z.execMatrix i j) = (Z.sourceSM8.matrix i j : ℂ) :=
        Z.execMatrix_bridge_to_SM8 i j
      _ = (Z.matrixReal i j : ℂ) := by
        rw [← Z.entryReal_eq_SM8 i j]
  entryReal_eq_SM8 := by
    intro i j
    exact Z.entryReal_eq_SM8 i j
  entryReal_eq_generatedLevelHistoryMatrix := by
    intro i j
    calc
      Z.matrixReal i j = Z.sourceSM8.matrix i j :=
        Z.entryReal_eq_SM8 i j
      _ = generatedLevelHistoryMatrixSM8 Z.sourceSM8.sourceBridge i j :=
        congrArg (fun M => M i j) Z.sourceSM8.matrix_eq_generatedLevelHistoryMatrix
  entryReal_eq_boundaryOperator := by
    intro i j
    exact Z.entryReal_eq_boundaryOperator i j
  entryReal_eq_SM6 := by
    intro i j
    exact Z.entryReal_eq_SM6 i j
  entryReal_eq_schur := by
    intro i j
    exact Z.entryReal_eq_schur i j
  execEntry_from_SM8Recheck := by
    intro i j
    rfl
  completionStatus := SM9aRecheckCompletionStatus.missingExecMirrorSourceClosedFromSM8Recheck
  completionStatus_eq := by
    rfl
  nextPhaseStatus := SM9aRecheckNextPhaseStatus.sm9bMayConsumeComputedExecMirror
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM9aRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatConversionStatus := SM9aRecheckNoRealToRatConversionStatus.noRealToRatConversion
  noRealToRatConversionStatus_eq := by
    rfl
  noScalarInverseStatus := SM9aRecheckNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM9aRecheckNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9aRecheckNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noTestMatrixStatus := SM9aRecheckNoTestMatrixStatus.noTestMatrix
  noTestMatrixStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM9aRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityStatus := SM9aRecheckNoProductIdentityStatus.noProductIdentity
  noProductIdentityStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM9aRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewCertificateStatus := SM9aRecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noNewCertificateStatus_eq := by
    rfl
  noDtnMultiSchurRecomputationStatus :=
    SM9aRecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noDtnMultiSchurRecomputationStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM9aRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem execMatrix_bridge_to_entryReal
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8Recheck.sourceSM8) :
    ExecComplexBridge.toComplex (Z.execMatrix i j) = (Z.entryReal i j : ℂ) :=
  Z.execMatrix_bridge_to_SM9a i j

theorem execEntry_from_SM8Recheck_thm
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8Recheck.sourceSM8) :
    Z.execMatrix i j = Z.sourceSM8Recheck.execMatrix i j :=
  Z.execEntry_from_SM8Recheck i j

theorem entryReal_from_generatedLevelHistoryMatrix
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8Recheck.sourceSM8) :
    Z.entryReal i j = generatedLevelHistoryMatrixSM8 Z.sourceSM8Recheck.sourceSM8.sourceBridge i j :=
  Z.entryReal_eq_generatedLevelHistoryMatrix i j

theorem entryReal_from_schur
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck Z.sourceSM8Recheck.sourceSM8) :
    Z.entryReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          Z.sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (Z.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex i)
        (Z.sourceSM8Recheck.sourceSM8.sourceBridge.toBoundaryIndex j) :=
  Z.entryReal_eq_schur i j

theorem missingSourceGate_closed_from_SM8Recheck
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G) :
    Z.completionStatus =
      SM9aRecheckCompletionStatus.missingExecMirrorSourceClosedFromSM8Recheck :=
  Z.completionStatus_eq

theorem nextPhase_SM9b_may_consume
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G) :
    Z.nextPhaseStatus = SM9aRecheckNextPhaseStatus.sm9bMayConsumeComputedExecMirror :=
  Z.nextPhaseStatus_eq

theorem no_forbidden_shortcuts
    (Z : GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a Cell p A P wp W E K T M S H G) :
    Z.noFreeExecMatrixStatus = SM9aRecheckNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    Z.noRealToRatConversionStatus = SM9aRecheckNoRealToRatConversionStatus.noRealToRatConversion ∧
    Z.noScalarInverseStatus = SM9aRecheckNoScalarInverseStatus.noScalarInverse ∧
    Z.noMatrixInvStatus = SM9aRecheckNoMatrixInvStatus.noMatrixInv ∧
    Z.noFieldSimpStatus = SM9aRecheckNoFieldSimpStatus.noFieldSimp ∧
    Z.noTestMatrixStatus = SM9aRecheckNoTestMatrixStatus.noTestMatrix ∧
    Z.noNewInverseOracleStatus = SM9aRecheckNoNewInverseOracleStatus.noNewInverseOracle ∧
    Z.noProductIdentityStatus = SM9aRecheckNoProductIdentityStatus.noProductIdentity ∧
    Z.noTwoSidedInvStatus = SM9aRecheckNoTwoSidedInvStatus.noTwoSidedInv ∧
    Z.noNewCertificateStatus = SM9aRecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate ∧
    Z.noDtnMultiSchurRecomputationStatus =
      SM9aRecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation ∧
    Z.noCharpolyDiscriminantHeegnerStatus =
      SM9aRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner :=
  ⟨Z.noFreeExecMatrixStatus_eq,
   Z.noRealToRatConversionStatus_eq,
   Z.noScalarInverseStatus_eq,
   Z.noMatrixInvStatus_eq,
   Z.noFieldSimpStatus_eq,
   Z.noTestMatrixStatus_eq,
   Z.noNewInverseOracleStatus_eq,
   Z.noProductIdentityStatus_eq,
   Z.noTwoSidedInvStatus_eq,
   Z.noNewCertificateStatus_eq,
   Z.noDtnMultiSchurRecomputationStatus_eq,
   Z.noCharpolyDiscriminantHeegnerStatus_eq⟩

end GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a

def regularGeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a.fromSM8Recheck L.regularExecMatrix

def variableGeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a.fromSM8Recheck L.variableExecMatrix

structure SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM8RecheckLedger : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableSource :
    GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularSource_eq_from_SM8Recheck :
    regularSource = regularGeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a sourceSM8RecheckLedger
  variableSource_eq_from_SM8Recheck :
    variableSource = variableGeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a sourceSM8RecheckLedger
  regularExecMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularSource.execMatrix i j) = (regularSource.entryReal i j : ℂ)
  variableExecMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableSource.execMatrix i j) = (variableSource.entryReal i j : ℂ)
  regularExecEntry_from_SM8Recheck : ∀ i j,
    regularSource.execMatrix i j = regularSource.sourceSM8Recheck.execMatrix i j
  variableExecEntry_from_SM8Recheck : ∀ i j,
    variableSource.execMatrix i j = variableSource.sourceSM8Recheck.execMatrix i j
  completionStatus : SM9aRecheckCompletionStatus
  completionStatus_eq :
    completionStatus = SM9aRecheckCompletionStatus.missingExecMirrorSourceClosedFromSM8Recheck
  nextPhaseStatus : SM9aRecheckNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9aRecheckNextPhaseStatus.sm9bMayConsumeComputedExecMirror
  noFreeExecMatrixStatus : SM9aRecheckNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM9aRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatConversionStatus : SM9aRecheckNoRealToRatConversionStatus
  noRealToRatConversionStatus_eq :
    noRealToRatConversionStatus = SM9aRecheckNoRealToRatConversionStatus.noRealToRatConversion
  noScalarInverseStatus : SM9aRecheckNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM9aRecheckNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM9aRecheckNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9aRecheckNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9aRecheckNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9aRecheckNoFieldSimpStatus.noFieldSimp
  noTestMatrixStatus : SM9aRecheckNoTestMatrixStatus
  noTestMatrixStatus_eq : noTestMatrixStatus = SM9aRecheckNoTestMatrixStatus.noTestMatrix
  noNewInverseOracleStatus : SM9aRecheckNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM9aRecheckNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityStatus : SM9aRecheckNoProductIdentityStatus
  noProductIdentityStatus_eq :
    noProductIdentityStatus = SM9aRecheckNoProductIdentityStatus.noProductIdentity
  noTwoSidedInvStatus : SM9aRecheckNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM9aRecheckNoTwoSidedInvStatus.noTwoSidedInv
  noNewCertificateStatus : SM9aRecheckNoNewCertificateStatus
  noNewCertificateStatus_eq :
    noNewCertificateStatus = SM9aRecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurRecomputationStatus : SM9aRecheckNoDtnMultiSchurRecomputationStatus
  noDtnMultiSchurRecomputationStatus_eq :
    noDtnMultiSchurRecomputationStatus =
      SM9aRecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
  noCharpolyDiscriminantHeegnerStatus : SM9aRecheckNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM9aRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner

def sm9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8RecheckGeneratedLevelHistoryExecMatrixLedger b β p regularWeight variableWeight) :
    SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight :=
  let R := regularGeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a L
  let V := variableGeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a L
  { sourceSM8RecheckLedger := L
    regularSource := R
    variableSource := V
    regularSource_eq_from_SM8Recheck := by
      rfl
    variableSource_eq_from_SM8Recheck := by
      rfl
    regularExecMatrixBridge := by
      intro i j
      exact R.execMatrix_bridge_to_SM9a i j
    variableExecMatrixBridge := by
      intro i j
      exact V.execMatrix_bridge_to_SM9a i j
    regularExecEntry_from_SM8Recheck := by
      intro i j
      exact R.execEntry_from_SM8Recheck i j
    variableExecEntry_from_SM8Recheck := by
      intro i j
      exact V.execEntry_from_SM8Recheck i j
    completionStatus := SM9aRecheckCompletionStatus.missingExecMirrorSourceClosedFromSM8Recheck
    completionStatus_eq := by
      rfl
    nextPhaseStatus := SM9aRecheckNextPhaseStatus.sm9bMayConsumeComputedExecMirror
    nextPhaseStatus_eq := by
      rfl
    noFreeExecMatrixStatus := SM9aRecheckNoFreeExecMatrixStatus.noFreeExecMatrix
    noFreeExecMatrixStatus_eq := by
      rfl
    noRealToRatConversionStatus := SM9aRecheckNoRealToRatConversionStatus.noRealToRatConversion
    noRealToRatConversionStatus_eq := by
      rfl
    noScalarInverseStatus := SM9aRecheckNoScalarInverseStatus.noScalarInverse
    noScalarInverseStatus_eq := by
      rfl
    noMatrixInvStatus := SM9aRecheckNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9aRecheckNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noTestMatrixStatus := SM9aRecheckNoTestMatrixStatus.noTestMatrix
    noTestMatrixStatus_eq := by
      rfl
    noNewInverseOracleStatus := SM9aRecheckNoNewInverseOracleStatus.noNewInverseOracle
    noNewInverseOracleStatus_eq := by
      rfl
    noProductIdentityStatus := SM9aRecheckNoProductIdentityStatus.noProductIdentity
    noProductIdentityStatus_eq := by
      rfl
    noTwoSidedInvStatus := SM9aRecheckNoTwoSidedInvStatus.noTwoSidedInv
    noTwoSidedInvStatus_eq := by
      rfl
    noNewCertificateStatus := SM9aRecheckNoNewCertificateStatus.noNewInteriorEliminationCertificate
    noNewCertificateStatus_eq := by
      rfl
    noDtnMultiSchurRecomputationStatus :=
      SM9aRecheckNoDtnMultiSchurRecomputationStatus.noDtnMultiSchurRecomputation
    noDtnMultiSchurRecomputationStatus_eq := by
      rfl
    noCharpolyDiscriminantHeegnerStatus :=
      SM9aRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner
    noCharpolyDiscriminantHeegnerStatus_eq := by
      rfl }

def sm9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight :=
  sm9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger
    (sm8RecheckGeneratedLevelHistoryExecMatrixLedger L level levelIndex)

theorem sm9aRecheck_regularExecMatrix_bridge
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck L.regularSource.sourceSM8Recheck.sourceSM8) :
    ExecComplexBridge.toComplex (L.regularSource.execMatrix i j) =
      (L.regularSource.entryReal i j : ℂ) :=
  L.regularExecMatrixBridge i j

theorem sm9aRecheck_variableExecMatrix_bridge
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (i j : GeneratedLevelHistoryExecMatrixIndexSM8Recheck L.variableSource.sourceSM8Recheck.sourceSM8) :
    ExecComplexBridge.toComplex (L.variableSource.execMatrix i j) =
      (L.variableSource.entryReal i j : ℂ) :=
  L.variableExecMatrixBridge i j

theorem sm9aRecheck_closed_from_SM8Recheck
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.completionStatus =
      SM9aRecheckCompletionStatus.missingExecMirrorSourceClosedFromSM8Recheck :=
  L.completionStatus_eq

theorem sm9aRecheck_nextPhase_SM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM9aRecheckNextPhaseStatus.sm9bMayConsumeComputedExecMirror :=
  L.nextPhaseStatus_eq

theorem sm9aRecheck_noMatrixInv
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.noMatrixInvStatus = SM9aRecheckNoMatrixInvStatus.noMatrixInv :=
  L.noMatrixInvStatus_eq

theorem sm9aRecheck_noCharpolyDiscriminantHeegner
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.noCharpolyDiscriminantHeegnerStatus =
      SM9aRecheckNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantHeegner :=
  L.noCharpolyDiscriminantHeegnerStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
