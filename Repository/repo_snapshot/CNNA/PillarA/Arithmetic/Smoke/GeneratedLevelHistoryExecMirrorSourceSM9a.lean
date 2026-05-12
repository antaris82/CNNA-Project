import CNNA.PillarA.Foundation.ExecComplexBridge
import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM9aSM8MatrixSourceStatus where
  | consumedGeneratedLevelHistoryMatrixFromBridgeSM8
  deriving DecidableEq, Repr

inductive SM9aExecMirrorConstructionStatus where
  | blockedMissingGeneratedRationalEntrySource
  deriving DecidableEq, Repr

inductive SM9aMissingGeneratedRationalEntrySourceStatus where
  | missingBeforeSM8AtGeneratedBoundarySchurEntryLayer
  deriving DecidableEq, Repr

inductive SM9aRationalProfileSourceStatus where
  | noGeneratedRationalProfileExposedForSM8Entry
  deriving DecidableEq, Repr

inductive SM9aEarliestNaturalBackfillStatus where
  | sm6bGeneratedLevelStepExecMirrorSource
  deriving DecidableEq, Repr

inductive SM9aNoFreeExecMatrixStatus where
  | noFreeExecComplexMatrixInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoRealToRatConversionStatus where
  | noRealToRatBackConversionInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoTestMatrixStatus where
  | noL2L3OrHandwrittenTestMatrixAsProvenanceInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoScalarInvStatus where
  | noScalarInvInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoMatrixInvStatus where
  | noMatrixInvInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoFieldSimpStatus where
  | noFieldSimpInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoCharpolyDiscriminantStatus where
  | noCharpolyFactorDiscriminantDataInSM9a
  deriving DecidableEq, Repr

inductive SM9aNoHeegnerTargetStatus where
  | noHeegnerTargetDecisionInSM9a
  deriving DecidableEq, Repr

inductive SM9aNextPhaseStatus where
  | sm6bGeneratedLevelStepExecMirrorSourceRequired
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

abbrev GeneratedLevelHistoryExecMirrorIndexSM9a
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G) :=
  GeneratedLevelHistoryMatrixIndexSM8 X.sourceBridge

structure GeneratedLevelHistoryExecMirrorWitnessSM9a
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
  sourceSM8Matrix : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G
  execMatrix : Matrix (GeneratedLevelHistoryExecMirrorIndexSM9a sourceSM8Matrix)
    (GeneratedLevelHistoryExecMirrorIndexSM9a sourceSM8Matrix) ExecComplex
  exec_entry_bridge : ∀ i j,
    ExecComplexBridge.toComplex (execMatrix i j) = (sourceSM8Matrix.matrix i j : ℂ)
  entry_eq_SM8 : ∀ i j,
    sourceSM8Matrix.matrix i j = generatedLevelHistoryMatrixSM8 sourceSM8Matrix.sourceBridge i j
  entry_eq_schur : ∀ i j,
    sourceSM8Matrix.matrix i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM8Matrix.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex i) (sourceSM8Matrix.sourceBridge.toBoundaryIndex j)

structure GeneratedLevelHistoryExecMirrorSourceSM9a
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
  sourceSM8Matrix : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G
  entryReal : GeneratedLevelHistoryExecMirrorIndexSM9a sourceSM8Matrix →
    GeneratedLevelHistoryExecMirrorIndexSM9a sourceSM8Matrix → ℝ
  entryReal_eq_SM8 : ∀ i j, entryReal i j = sourceSM8Matrix.matrix i j
  entryReal_eq_generatedLevelHistoryMatrix : ∀ i j,
    entryReal i j = generatedLevelHistoryMatrixSM8 sourceSM8Matrix.sourceBridge i j
  entryReal_eq_boundaryOperator : ∀ i j,
    entryReal i j =
      sourceSM8Matrix.sourceBridge.sourceSM6Witness.boundaryOperator
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex i)
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex j)
  entryReal_eq_SM6 : ∀ i j,
    entryReal i j =
      sourceSM8Matrix.sourceBridge.sourceSM6Witness.source.boundaryOperator
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex i)
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex j)
  entryReal_eq_schur : ∀ i j,
    entryReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM8Matrix.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex i)
        (sourceSM8Matrix.sourceBridge.toBoundaryIndex j)
  sm8MatrixSourceStatus : SM9aSM8MatrixSourceStatus
  sm8MatrixSourceStatus_eq :
    sm8MatrixSourceStatus =
      SM9aSM8MatrixSourceStatus.consumedGeneratedLevelHistoryMatrixFromBridgeSM8
  execMirrorConstructionStatus : SM9aExecMirrorConstructionStatus
  execMirrorConstructionStatus_eq :
    execMirrorConstructionStatus =
      SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource
  missingGeneratedRationalEntrySourceStatus : SM9aMissingGeneratedRationalEntrySourceStatus
  missingGeneratedRationalEntrySourceStatus_eq :
    missingGeneratedRationalEntrySourceStatus =
      SM9aMissingGeneratedRationalEntrySourceStatus.missingBeforeSM8AtGeneratedBoundarySchurEntryLayer
  rationalProfileSourceStatus : SM9aRationalProfileSourceStatus
  rationalProfileSourceStatus_eq :
    rationalProfileSourceStatus =
      SM9aRationalProfileSourceStatus.noGeneratedRationalProfileExposedForSM8Entry
  earliestNaturalBackfillStatus : SM9aEarliestNaturalBackfillStatus
  earliestNaturalBackfillStatus_eq :
    earliestNaturalBackfillStatus =
      SM9aEarliestNaturalBackfillStatus.sm6bGeneratedLevelStepExecMirrorSource
  noFreeExecMatrixStatus : SM9aNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM9aNoFreeExecMatrixStatus.noFreeExecComplexMatrixInSM9a
  noRealToRatConversionStatus : SM9aNoRealToRatConversionStatus
  noRealToRatConversionStatus_eq :
    noRealToRatConversionStatus =
      SM9aNoRealToRatConversionStatus.noRealToRatBackConversionInSM9a
  noTestMatrixStatus : SM9aNoTestMatrixStatus
  noTestMatrixStatus_eq :
    noTestMatrixStatus =
      SM9aNoTestMatrixStatus.noL2L3OrHandwrittenTestMatrixAsProvenanceInSM9a
  noScalarInvStatus : SM9aNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9aNoScalarInvStatus.noScalarInvInSM9a
  noMatrixInvStatus : SM9aNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9aNoMatrixInvStatus.noMatrixInvInSM9a
  noFieldSimpStatus : SM9aNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9aNoFieldSimpStatus.noFieldSimpInSM9a
  noCharpolyDiscriminantStatus : SM9aNoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM9aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM9a
  noHeegnerTargetStatus : SM9aNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9aNoHeegnerTargetStatus.noHeegnerTargetDecisionInSM9a
  nextPhaseStatus : SM9aNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9aNextPhaseStatus.sm6bGeneratedLevelStepExecMirrorSourceRequired

namespace GeneratedLevelHistoryExecMirrorSourceSM9a

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

def fromSM8
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G where
  sourceSM8Matrix := X
  entryReal := X.matrix
  entryReal_eq_SM8 := by
    intro i j
    rfl
  entryReal_eq_generatedLevelHistoryMatrix := by
    intro i j
    exact congrArg (fun M => M i j) X.matrix_eq_generatedLevelHistoryMatrix
  entryReal_eq_boundaryOperator := by
    intro i j
    exact X.entry_eq_boundaryOperator i j
  entryReal_eq_SM6 := by
    intro i j
    exact X.entry_eq_SM6 i j
  entryReal_eq_schur := by
    intro i j
    exact X.entry_eq_schur i j
  sm8MatrixSourceStatus :=
    SM9aSM8MatrixSourceStatus.consumedGeneratedLevelHistoryMatrixFromBridgeSM8
  sm8MatrixSourceStatus_eq := by
    rfl
  execMirrorConstructionStatus :=
    SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource
  execMirrorConstructionStatus_eq := by
    rfl
  missingGeneratedRationalEntrySourceStatus :=
    SM9aMissingGeneratedRationalEntrySourceStatus.missingBeforeSM8AtGeneratedBoundarySchurEntryLayer
  missingGeneratedRationalEntrySourceStatus_eq := by
    rfl
  rationalProfileSourceStatus :=
    SM9aRationalProfileSourceStatus.noGeneratedRationalProfileExposedForSM8Entry
  rationalProfileSourceStatus_eq := by
    rfl
  earliestNaturalBackfillStatus :=
    SM9aEarliestNaturalBackfillStatus.sm6bGeneratedLevelStepExecMirrorSource
  earliestNaturalBackfillStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM9aNoFreeExecMatrixStatus.noFreeExecComplexMatrixInSM9a
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatConversionStatus :=
    SM9aNoRealToRatConversionStatus.noRealToRatBackConversionInSM9a
  noRealToRatConversionStatus_eq := by
    rfl
  noTestMatrixStatus :=
    SM9aNoTestMatrixStatus.noL2L3OrHandwrittenTestMatrixAsProvenanceInSM9a
  noTestMatrixStatus_eq := by
    rfl
  noScalarInvStatus := SM9aNoScalarInvStatus.noScalarInvInSM9a
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus := SM9aNoMatrixInvStatus.noMatrixInvInSM9a
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9aNoFieldSimpStatus.noFieldSimpInSM9a
  noFieldSimpStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM9aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM9a
  noCharpolyDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9aNoHeegnerTargetStatus.noHeegnerTargetDecisionInSM9a
  noHeegnerTargetStatus_eq := by
    rfl
  nextPhaseStatus := SM9aNextPhaseStatus.sm6bGeneratedLevelStepExecMirrorSourceRequired
  nextPhaseStatus_eq := by
    rfl

theorem entryReal_from_SM8
    (Y : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMirrorIndexSM9a Y.sourceSM8Matrix) :
    Y.entryReal i j = Y.sourceSM8Matrix.matrix i j :=
  Y.entryReal_eq_SM8 i j

theorem entryReal_from_generatedLevelHistoryMatrix
    (Y : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMirrorIndexSM9a Y.sourceSM8Matrix) :
    Y.entryReal i j = generatedLevelHistoryMatrixSM8 Y.sourceSM8Matrix.sourceBridge i j :=
  Y.entryReal_eq_generatedLevelHistoryMatrix i j

theorem entryReal_from_schur
    (Y : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryExecMirrorIndexSM9a Y.sourceSM8Matrix) :
    Y.entryReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          Y.sourceSM8Matrix.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (Y.sourceSM8Matrix.sourceBridge.toBoundaryIndex i)
        (Y.sourceSM8Matrix.sourceBridge.toBoundaryIndex j) :=
  Y.entryReal_eq_schur i j

theorem execMirror_blocked_missingGeneratedRationalEntrySource
    (Y : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G) :
    Y.execMirrorConstructionStatus =
      SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource :=
  Y.execMirrorConstructionStatus_eq

theorem earliestBackfill_is_SM6b
    (Y : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G) :
    Y.earliestNaturalBackfillStatus =
      SM9aEarliestNaturalBackfillStatus.sm6bGeneratedLevelStepExecMirrorSource :=
  Y.earliestNaturalBackfillStatus_eq

theorem nextPhase_is_SM6b
    (Y : GeneratedLevelHistoryExecMirrorSourceSM9a Cell p A P wp W E K T M S H G) :
    Y.nextPhaseStatus = SM9aNextPhaseStatus.sm6bGeneratedLevelStepExecMirrorSourceRequired :=
  Y.nextPhaseStatus_eq

end GeneratedLevelHistoryExecMirrorSourceSM9a

def regularGeneratedLevelHistoryExecMirrorSourceSM9a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryExecMirrorSourceSM9a
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryExecMirrorSourceSM9a.fromSM8 L.regularMatrix

def variableGeneratedLevelHistoryExecMirrorSourceSM9a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryExecMirrorSourceSM9a
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryExecMirrorSourceSM9a.fromSM8 L.variableMatrix

structure SM9aGeneratedLevelHistoryExecMirrorSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM8Ledger : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedLevelHistoryExecMirrorSourceSM9a
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
  variableSource :
    GeneratedLevelHistoryExecMirrorSourceSM9a
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
  regularSource_eq_from_SM8 :
    regularSource = regularGeneratedLevelHistoryExecMirrorSourceSM9a sourceSM8Ledger
  variableSource_eq_from_SM8 :
    variableSource = variableGeneratedLevelHistoryExecMirrorSourceSM9a sourceSM8Ledger
  regularConstructionStatus : SM9aExecMirrorConstructionStatus
  regularConstructionStatus_eq :
    regularConstructionStatus =
      SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource
  variableConstructionStatus : SM9aExecMirrorConstructionStatus
  variableConstructionStatus_eq :
    variableConstructionStatus =
      SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource
  missingGeneratedRationalEntrySourceStatus : SM9aMissingGeneratedRationalEntrySourceStatus
  missingGeneratedRationalEntrySourceStatus_eq :
    missingGeneratedRationalEntrySourceStatus =
      SM9aMissingGeneratedRationalEntrySourceStatus.missingBeforeSM8AtGeneratedBoundarySchurEntryLayer
  rationalProfileSourceStatus : SM9aRationalProfileSourceStatus
  rationalProfileSourceStatus_eq :
    rationalProfileSourceStatus =
      SM9aRationalProfileSourceStatus.noGeneratedRationalProfileExposedForSM8Entry
  earliestNaturalBackfillStatus : SM9aEarliestNaturalBackfillStatus
  earliestNaturalBackfillStatus_eq :
    earliestNaturalBackfillStatus =
      SM9aEarliestNaturalBackfillStatus.sm6bGeneratedLevelStepExecMirrorSource
  noFreeExecMatrixStatus : SM9aNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq :
    noFreeExecMatrixStatus = SM9aNoFreeExecMatrixStatus.noFreeExecComplexMatrixInSM9a
  noRealToRatConversionStatus : SM9aNoRealToRatConversionStatus
  noRealToRatConversionStatus_eq :
    noRealToRatConversionStatus =
      SM9aNoRealToRatConversionStatus.noRealToRatBackConversionInSM9a
  noTestMatrixStatus : SM9aNoTestMatrixStatus
  noTestMatrixStatus_eq :
    noTestMatrixStatus =
      SM9aNoTestMatrixStatus.noL2L3OrHandwrittenTestMatrixAsProvenanceInSM9a
  noScalarInvStatus : SM9aNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9aNoScalarInvStatus.noScalarInvInSM9a
  noMatrixInvStatus : SM9aNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9aNoMatrixInvStatus.noMatrixInvInSM9a
  noFieldSimpStatus : SM9aNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9aNoFieldSimpStatus.noFieldSimpInSM9a
  noCharpolyDiscriminantStatus : SM9aNoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM9aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM9a
  noHeegnerTargetStatus : SM9aNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq :
    noHeegnerTargetStatus = SM9aNoHeegnerTargetStatus.noHeegnerTargetDecisionInSM9a
  nextPhaseStatus : SM9aNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9aNextPhaseStatus.sm6bGeneratedLevelStepExecMirrorSourceRequired

def sm9aGeneratedLevelHistoryExecMirrorSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight where
  sourceSM8Ledger := L
  regularSource := regularGeneratedLevelHistoryExecMirrorSourceSM9a L
  variableSource := variableGeneratedLevelHistoryExecMirrorSourceSM9a L
  regularSource_eq_from_SM8 := by
    rfl
  variableSource_eq_from_SM8 := by
    rfl
  regularConstructionStatus :=
    SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource
  regularConstructionStatus_eq := by
    rfl
  variableConstructionStatus :=
    SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource
  variableConstructionStatus_eq := by
    rfl
  missingGeneratedRationalEntrySourceStatus :=
    SM9aMissingGeneratedRationalEntrySourceStatus.missingBeforeSM8AtGeneratedBoundarySchurEntryLayer
  missingGeneratedRationalEntrySourceStatus_eq := by
    rfl
  rationalProfileSourceStatus :=
    SM9aRationalProfileSourceStatus.noGeneratedRationalProfileExposedForSM8Entry
  rationalProfileSourceStatus_eq := by
    rfl
  earliestNaturalBackfillStatus :=
    SM9aEarliestNaturalBackfillStatus.sm6bGeneratedLevelStepExecMirrorSource
  earliestNaturalBackfillStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM9aNoFreeExecMatrixStatus.noFreeExecComplexMatrixInSM9a
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatConversionStatus :=
    SM9aNoRealToRatConversionStatus.noRealToRatBackConversionInSM9a
  noRealToRatConversionStatus_eq := by
    rfl
  noTestMatrixStatus :=
    SM9aNoTestMatrixStatus.noL2L3OrHandwrittenTestMatrixAsProvenanceInSM9a
  noTestMatrixStatus_eq := by
    rfl
  noScalarInvStatus := SM9aNoScalarInvStatus.noScalarInvInSM9a
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus := SM9aNoMatrixInvStatus.noMatrixInvInSM9a
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9aNoFieldSimpStatus.noFieldSimpInSM9a
  noFieldSimpStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM9aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM9a
  noCharpolyDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9aNoHeegnerTargetStatus.noHeegnerTargetDecisionInSM9a
  noHeegnerTargetStatus_eq := by
    rfl
  nextPhaseStatus := SM9aNextPhaseStatus.sm6bGeneratedLevelStepExecMirrorSourceRequired
  nextPhaseStatus_eq := by
    rfl

def sm9aGeneratedLevelHistoryExecMirrorSourceLedger_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight :=
  sm9aGeneratedLevelHistoryExecMirrorSourceLedger
    (sm8GeneratedLevelHistoryMatrixLedger_from_SM5 L level levelIndex)

theorem sm9a_regularConstruction_blocked_missingSource
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.regularConstructionStatus =
      SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource :=
  L.regularConstructionStatus_eq

theorem sm9a_variableConstruction_blocked_missingSource
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.variableConstructionStatus =
      SM9aExecMirrorConstructionStatus.blockedMissingGeneratedRationalEntrySource :=
  L.variableConstructionStatus_eq

theorem sm9a_earliestBackfill_is_SM6b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.earliestNaturalBackfillStatus =
      SM9aEarliestNaturalBackfillStatus.sm6bGeneratedLevelStepExecMirrorSource :=
  L.earliestNaturalBackfillStatus_eq

theorem sm9a_nextPhase_is_SM6b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM9aNextPhaseStatus.sm6bGeneratedLevelStepExecMirrorSourceRequired :=
  L.nextPhaseStatus_eq

theorem sm9a_noCharpolyDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.noCharpolyDiscriminantStatus =
      SM9aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM9a :=
  L.noCharpolyDiscriminantStatus_eq

theorem sm9a_noHeegnerTarget
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.noHeegnerTargetStatus = SM9aNoHeegnerTargetStatus.noHeegnerTargetDecisionInSM9a :=
  L.noHeegnerTargetStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
