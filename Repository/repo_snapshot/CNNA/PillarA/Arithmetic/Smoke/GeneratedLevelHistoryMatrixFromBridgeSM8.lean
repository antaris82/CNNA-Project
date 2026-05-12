import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u v

inductive SM8BridgeSourceStatus where
  | consumedSM7BridgeRecheckBridge
  deriving DecidableEq, Repr

inductive SM8MatrixProvenanceStatus where
  | pullbackOfSM6SM5SchurBoundaryOperator
  deriving DecidableEq, Repr

inductive SM8NoNewBoundaryPortSourceStatus where
  | noNewBoundaryPortSourceInSM8
  deriving DecidableEq, Repr

inductive SM8NoFreeFintypeEnumerationStatus where
  | noFreeFintypeEnumerationInSM8
  deriving DecidableEq, Repr

inductive SM8NoFreeTableStatus where
  | noFreeTableInSM8
  deriving DecidableEq, Repr

inductive SM8NoFreeLevelHistoryMatrixPackageStatus where
  | noFreeLevelHistoryMatrixPackageMatrixInSM8
  deriving DecidableEq, Repr

inductive SM8NoChoiceStatus where
  | noChoiceInSM8
  deriving DecidableEq, Repr

inductive SM8NoMatrixInvStatus where
  | noMatrixInvIntroducedInSM8
  deriving DecidableEq, Repr

inductive SM8NoCharpolyDiscriminantStatus where
  | noCharpolyFactorDiscriminantDataInSM8
  deriving DecidableEq, Repr

inductive SM8NoHigherLevelScanStatus where
  | noHigherLevelScanInSM8
  deriving DecidableEq, Repr

inductive SM8NextPhaseStatus where
  | matrixSurfaceOnlyBeforeArithmeticTargets
  deriving DecidableEq, Repr

theorem matrix_entry_of_eq
    {ι κ : Type u} {R : Type v} {A B : Matrix ι κ R}
    (h : A = B) (i : ι) (j : κ) :
    A i j = B i j :=
  congrArg (fun M => M i j) h

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

abbrev GeneratedLevelHistoryMatrixIndexSM8
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G) :=
  GeneratedLevelHistoryIndexSM6 B.sourceSM6Witness.level

def generatedSchurEntrySM8
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) : ℝ :=
  B.sourceSM6Witness.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j)

def generatedLevelHistoryMatrixSM8
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G) :
    Matrix (GeneratedLevelHistoryMatrixIndexSM8 B) (GeneratedLevelHistoryMatrixIndexSM8 B) ℝ :=
  fun i j => generatedSchurEntrySM8 B i j

theorem generatedSchurEntrySM8_eq_boundaryOperator
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedSchurEntrySM8 B i j =
      B.sourceSM6Witness.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j) := by
  rfl

theorem generatedLevelHistoryMatrixSM8_apply
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedLevelHistoryMatrixSM8 B i j = generatedSchurEntrySM8 B i j := by
  rfl

theorem generatedLevelHistoryMatrixSM8_entry_eq_boundaryOperator
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedLevelHistoryMatrixSM8 B i j =
      B.sourceSM6Witness.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j) := by
  rfl

theorem generatedSchurEntrySM8_eq_SM6
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedSchurEntrySM8 B i j =
      B.sourceSM6Witness.source.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j) := by
  change
    B.sourceSM6Witness.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j) =
      B.sourceSM6Witness.source.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j)
  exact matrix_entry_of_eq B.boundaryOperator_from_SM6 (B.toBoundaryIndex i) (B.toBoundaryIndex j)

theorem generatedLevelHistoryMatrixSM8_entry_eq_SM6
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedLevelHistoryMatrixSM8 B i j =
      B.sourceSM6Witness.source.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j) := by
  change generatedSchurEntrySM8 B i j =
    B.sourceSM6Witness.source.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j)
  exact generatedSchurEntrySM8_eq_SM6 B i j

theorem generatedSchurEntrySM8_eq_schur
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedSchurEntrySM8 B i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          B.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (B.toBoundaryIndex i) (B.toBoundaryIndex j) := by
  change
    B.sourceSM6Witness.boundaryOperator (B.toBoundaryIndex i) (B.toBoundaryIndex j) =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          B.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (B.toBoundaryIndex i) (B.toBoundaryIndex j)
  exact matrix_entry_of_eq B.boundaryOperator_from_schur (B.toBoundaryIndex i) (B.toBoundaryIndex j)

theorem generatedLevelHistoryMatrixSM8_entry_eq_schur
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 B) :
    generatedLevelHistoryMatrixSM8 B i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          B.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (B.toBoundaryIndex i) (B.toBoundaryIndex j) := by
  change generatedSchurEntrySM8 B i j =
    (generatedBoundaryBlockSM3fR W -
      generatedBoundaryInteriorBlockSM3fR W *
        B.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
        generatedInteriorBoundaryBlockSM3fR W)
      (B.toBoundaryIndex i) (B.toBoundaryIndex j)
  exact generatedSchurEntrySM8_eq_schur B i j

structure GeneratedLevelHistoryMatrixFromBridgeSM8
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
  sourceBridge : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G
  matrix : Matrix (GeneratedLevelHistoryMatrixIndexSM8 sourceBridge)
    (GeneratedLevelHistoryMatrixIndexSM8 sourceBridge) ℝ
  matrix_eq_generatedLevelHistoryMatrix : matrix = generatedLevelHistoryMatrixSM8 sourceBridge
  entry_eq_boundaryOperator : ∀ i j,
    matrix i j =
      sourceBridge.sourceSM6Witness.boundaryOperator
        (sourceBridge.toBoundaryIndex i) (sourceBridge.toBoundaryIndex j)
  entry_eq_SM6 : ∀ i j,
    matrix i j =
      sourceBridge.sourceSM6Witness.source.boundaryOperator
        (sourceBridge.toBoundaryIndex i) (sourceBridge.toBoundaryIndex j)
  entry_eq_schur : ∀ i j,
    matrix i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (sourceBridge.toBoundaryIndex i) (sourceBridge.toBoundaryIndex j)
  bridgeSourceStatus : SM8BridgeSourceStatus
  bridgeSourceStatus_eq :
    bridgeSourceStatus = SM8BridgeSourceStatus.consumedSM7BridgeRecheckBridge
  matrixProvenanceStatus : SM8MatrixProvenanceStatus
  matrixProvenanceStatus_eq :
    matrixProvenanceStatus = SM8MatrixProvenanceStatus.pullbackOfSM6SM5SchurBoundaryOperator
  noNewBoundaryPortSourceStatus : SM8NoNewBoundaryPortSourceStatus
  noNewBoundaryPortSourceStatus_eq :
    noNewBoundaryPortSourceStatus = SM8NoNewBoundaryPortSourceStatus.noNewBoundaryPortSourceInSM8
  noFreeFintypeEnumerationStatus : SM8NoFreeFintypeEnumerationStatus
  noFreeFintypeEnumerationStatus_eq :
    noFreeFintypeEnumerationStatus = SM8NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM8
  noFreeTableStatus : SM8NoFreeTableStatus
  noFreeTableStatus_eq : noFreeTableStatus = SM8NoFreeTableStatus.noFreeTableInSM8
  noFreeLevelHistoryMatrixPackageStatus : SM8NoFreeLevelHistoryMatrixPackageStatus
  noFreeLevelHistoryMatrixPackageStatus_eq :
    noFreeLevelHistoryMatrixPackageStatus =
      SM8NoFreeLevelHistoryMatrixPackageStatus.noFreeLevelHistoryMatrixPackageMatrixInSM8
  noChoiceStatus : SM8NoChoiceStatus
  noChoiceStatus_eq : noChoiceStatus = SM8NoChoiceStatus.noChoiceInSM8
  noMatrixInvStatus : SM8NoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM8NoMatrixInvStatus.noMatrixInvIntroducedInSM8
  noCharpolyDiscriminantStatus : SM8NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM8NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM8
  noHigherLevelScanStatus : SM8NoHigherLevelScanStatus
  noHigherLevelScanStatus_eq :
    noHigherLevelScanStatus = SM8NoHigherLevelScanStatus.noHigherLevelScanInSM8
  nextPhaseStatus : SM8NextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM8NextPhaseStatus.matrixSurfaceOnlyBeforeArithmeticTargets

namespace GeneratedLevelHistoryMatrixFromBridgeSM8

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

def fromBridge
    (B : GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G where
  sourceBridge := B
  matrix := generatedLevelHistoryMatrixSM8 B
  matrix_eq_generatedLevelHistoryMatrix := by
    rfl
  entry_eq_boundaryOperator := by
    intro i j
    rfl
  entry_eq_SM6 := by
    intro i j
    exact generatedLevelHistoryMatrixSM8_entry_eq_SM6 B i j
  entry_eq_schur := by
    intro i j
    exact generatedLevelHistoryMatrixSM8_entry_eq_schur B i j
  bridgeSourceStatus := SM8BridgeSourceStatus.consumedSM7BridgeRecheckBridge
  bridgeSourceStatus_eq := by
    rfl
  matrixProvenanceStatus := SM8MatrixProvenanceStatus.pullbackOfSM6SM5SchurBoundaryOperator
  matrixProvenanceStatus_eq := by
    rfl
  noNewBoundaryPortSourceStatus := SM8NoNewBoundaryPortSourceStatus.noNewBoundaryPortSourceInSM8
  noNewBoundaryPortSourceStatus_eq := by
    rfl
  noFreeFintypeEnumerationStatus := SM8NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM8
  noFreeFintypeEnumerationStatus_eq := by
    rfl
  noFreeTableStatus := SM8NoFreeTableStatus.noFreeTableInSM8
  noFreeTableStatus_eq := by
    rfl
  noFreeLevelHistoryMatrixPackageStatus :=
    SM8NoFreeLevelHistoryMatrixPackageStatus.noFreeLevelHistoryMatrixPackageMatrixInSM8
  noFreeLevelHistoryMatrixPackageStatus_eq := by
    rfl
  noChoiceStatus := SM8NoChoiceStatus.noChoiceInSM8
  noChoiceStatus_eq := by
    rfl
  noMatrixInvStatus := SM8NoMatrixInvStatus.noMatrixInvIntroducedInSM8
  noMatrixInvStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM8NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM8
  noCharpolyDiscriminantStatus_eq := by
    rfl
  noHigherLevelScanStatus := SM8NoHigherLevelScanStatus.noHigherLevelScanInSM8
  noHigherLevelScanStatus_eq := by
    rfl
  nextPhaseStatus := SM8NextPhaseStatus.matrixSurfaceOnlyBeforeArithmeticTargets
  nextPhaseStatus_eq := by
    rfl

theorem matrix_from_bridge
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G) :
    X.matrix = generatedLevelHistoryMatrixSM8 X.sourceBridge :=
  X.matrix_eq_generatedLevelHistoryMatrix

theorem matrix_entry_eq_boundaryOperator
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 X.sourceBridge) :
    X.matrix i j =
      X.sourceBridge.sourceSM6Witness.boundaryOperator
        (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j) :=
  X.entry_eq_boundaryOperator i j

theorem matrix_entry_eq_SM6
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 X.sourceBridge) :
    X.matrix i j =
      X.sourceBridge.sourceSM6Witness.source.boundaryOperator
        (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j) :=
  X.entry_eq_SM6 i j

theorem matrix_entry_eq_schur
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G)
    (i j : GeneratedLevelHistoryMatrixIndexSM8 X.sourceBridge) :
    X.matrix i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          X.sourceBridge.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W)
        (X.sourceBridge.toBoundaryIndex i) (X.sourceBridge.toBoundaryIndex j) :=
  X.entry_eq_schur i j

theorem noMatrixInv_for_SM8
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G) :
    X.noMatrixInvStatus = SM8NoMatrixInvStatus.noMatrixInvIntroducedInSM8 :=
  X.noMatrixInvStatus_eq

theorem noCharpolyDiscriminant_for_SM8
    (X : GeneratedLevelHistoryMatrixFromBridgeSM8 Cell p A P wp W E K T M S H G) :
    X.noCharpolyDiscriminantStatus =
      SM8NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM8 :=
  X.noCharpolyDiscriminantStatus_eq

end GeneratedLevelHistoryMatrixFromBridgeSM8

def regularGeneratedLevelHistoryMatrixFromBridgeSM8
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryMatrixFromBridgeSM8
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryMatrixFromBridgeSM8.fromBridge L.regularBridge

def variableGeneratedLevelHistoryMatrixFromBridgeSM8
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryMatrixFromBridgeSM8
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryMatrixFromBridgeSM8.fromBridge L.variableBridge

structure SM8GeneratedLevelHistoryMatrixLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM7BridgeRecheckLedger : SM7BridgeRecheckLedger b β p regularWeight variableWeight
  regularMatrix :
    GeneratedLevelHistoryMatrixFromBridgeSM8
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableMatrix :
    GeneratedLevelHistoryMatrixFromBridgeSM8
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularMatrix_eq_from_bridge :
    regularMatrix = regularGeneratedLevelHistoryMatrixFromBridgeSM8 sourceSM7BridgeRecheckLedger
  variableMatrix_eq_from_bridge :
    variableMatrix = variableGeneratedLevelHistoryMatrixFromBridgeSM8 sourceSM7BridgeRecheckLedger
  regularBridgeOutcome : SM7BridgeOutcome
  regularBridgeOutcome_eq : regularBridgeOutcome = SM7BridgeOutcome.bridgeSuccess
  variableBridgeOutcome : SM7BridgeOutcome
  variableBridgeOutcome_eq : variableBridgeOutcome = SM7BridgeOutcome.bridgeSuccess
  regularMatrixProvenanceStatus : SM8MatrixProvenanceStatus
  regularMatrixProvenanceStatus_eq :
    regularMatrixProvenanceStatus =
      SM8MatrixProvenanceStatus.pullbackOfSM6SM5SchurBoundaryOperator
  variableMatrixProvenanceStatus : SM8MatrixProvenanceStatus
  variableMatrixProvenanceStatus_eq :
    variableMatrixProvenanceStatus =
      SM8MatrixProvenanceStatus.pullbackOfSM6SM5SchurBoundaryOperator
  noNewBoundaryPortSourceStatus : SM8NoNewBoundaryPortSourceStatus
  noNewBoundaryPortSourceStatus_eq :
    noNewBoundaryPortSourceStatus = SM8NoNewBoundaryPortSourceStatus.noNewBoundaryPortSourceInSM8
  noFreeFintypeEnumerationStatus : SM8NoFreeFintypeEnumerationStatus
  noFreeFintypeEnumerationStatus_eq :
    noFreeFintypeEnumerationStatus = SM8NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM8
  noFreeTableStatus : SM8NoFreeTableStatus
  noFreeTableStatus_eq : noFreeTableStatus = SM8NoFreeTableStatus.noFreeTableInSM8
  noFreeLevelHistoryMatrixPackageStatus : SM8NoFreeLevelHistoryMatrixPackageStatus
  noFreeLevelHistoryMatrixPackageStatus_eq :
    noFreeLevelHistoryMatrixPackageStatus =
      SM8NoFreeLevelHistoryMatrixPackageStatus.noFreeLevelHistoryMatrixPackageMatrixInSM8
  noChoiceStatus : SM8NoChoiceStatus
  noChoiceStatus_eq : noChoiceStatus = SM8NoChoiceStatus.noChoiceInSM8
  noMatrixInvStatus : SM8NoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM8NoMatrixInvStatus.noMatrixInvIntroducedInSM8
  noCharpolyDiscriminantStatus : SM8NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM8NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM8
  noHigherLevelScanStatus : SM8NoHigherLevelScanStatus
  noHigherLevelScanStatus_eq :
    noHigherLevelScanStatus = SM8NoHigherLevelScanStatus.noHigherLevelScanInSM8
  nextPhaseStatus : SM8NextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM8NextPhaseStatus.matrixSurfaceOnlyBeforeArithmeticTargets

def sm8GeneratedLevelHistoryMatrixLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight where
  sourceSM7BridgeRecheckLedger := L
  regularMatrix := regularGeneratedLevelHistoryMatrixFromBridgeSM8 L
  variableMatrix := variableGeneratedLevelHistoryMatrixFromBridgeSM8 L
  regularMatrix_eq_from_bridge := by
    rfl
  variableMatrix_eq_from_bridge := by
    rfl
  regularBridgeOutcome := L.regularOutcome
  regularBridgeOutcome_eq := by
    exact L.regularOutcome_eq
  variableBridgeOutcome := L.variableOutcome
  variableBridgeOutcome_eq := by
    exact L.variableOutcome_eq
  regularMatrixProvenanceStatus := SM8MatrixProvenanceStatus.pullbackOfSM6SM5SchurBoundaryOperator
  regularMatrixProvenanceStatus_eq := by
    rfl
  variableMatrixProvenanceStatus := SM8MatrixProvenanceStatus.pullbackOfSM6SM5SchurBoundaryOperator
  variableMatrixProvenanceStatus_eq := by
    rfl
  noNewBoundaryPortSourceStatus := SM8NoNewBoundaryPortSourceStatus.noNewBoundaryPortSourceInSM8
  noNewBoundaryPortSourceStatus_eq := by
    rfl
  noFreeFintypeEnumerationStatus := SM8NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM8
  noFreeFintypeEnumerationStatus_eq := by
    rfl
  noFreeTableStatus := SM8NoFreeTableStatus.noFreeTableInSM8
  noFreeTableStatus_eq := by
    rfl
  noFreeLevelHistoryMatrixPackageStatus :=
    SM8NoFreeLevelHistoryMatrixPackageStatus.noFreeLevelHistoryMatrixPackageMatrixInSM8
  noFreeLevelHistoryMatrixPackageStatus_eq := by
    rfl
  noChoiceStatus := SM8NoChoiceStatus.noChoiceInSM8
  noChoiceStatus_eq := by
    rfl
  noMatrixInvStatus := SM8NoMatrixInvStatus.noMatrixInvIntroducedInSM8
  noMatrixInvStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM8NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM8
  noCharpolyDiscriminantStatus_eq := by
    rfl
  noHigherLevelScanStatus := SM8NoHigherLevelScanStatus.noHigherLevelScanInSM8
  noHigherLevelScanStatus_eq := by
    rfl
  nextPhaseStatus := SM8NextPhaseStatus.matrixSurfaceOnlyBeforeArithmeticTargets
  nextPhaseStatus_eq := by
    rfl

def sm8GeneratedLevelHistoryMatrixLedger_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight :=
  sm8GeneratedLevelHistoryMatrixLedger
    (sm7BridgeRecheckLedger_from_SM5 L level levelIndex)

theorem sm8_regularBridgeOutcome_success
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    L.regularBridgeOutcome = SM7BridgeOutcome.bridgeSuccess :=
  L.regularBridgeOutcome_eq

theorem sm8_variableBridgeOutcome_success
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    L.variableBridgeOutcome = SM7BridgeOutcome.bridgeSuccess :=
  L.variableBridgeOutcome_eq

theorem sm8_regularMatrix_from_bridge
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    L.regularMatrix = regularGeneratedLevelHistoryMatrixFromBridgeSM8 L.sourceSM7BridgeRecheckLedger :=
  L.regularMatrix_eq_from_bridge

theorem sm8_variableMatrix_from_bridge
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    L.variableMatrix = variableGeneratedLevelHistoryMatrixFromBridgeSM8 L.sourceSM7BridgeRecheckLedger :=
  L.variableMatrix_eq_from_bridge

theorem sm8_noMatrixInv
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    L.noMatrixInvStatus = SM8NoMatrixInvStatus.noMatrixInvIntroducedInSM8 :=
  L.noMatrixInvStatus_eq

theorem sm8_noCharpolyDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM8GeneratedLevelHistoryMatrixLedger b β p regularWeight variableWeight) :
    L.noCharpolyDiscriminantStatus =
      SM8NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM8 :=
  L.noCharpolyDiscriminantStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
