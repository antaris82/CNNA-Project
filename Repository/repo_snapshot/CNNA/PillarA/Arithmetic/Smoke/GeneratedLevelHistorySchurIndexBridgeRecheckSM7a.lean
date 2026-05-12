import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a
import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM7BridgeRecheckSourceStatus where
  | consumedSM6aBoundaryPortSource
  deriving DecidableEq, Repr

inductive SM7BridgeRecheckSM8GateStatus where
  | sm8ReleasedAfterRegularVariableBridgeSuccess
  deriving DecidableEq, Repr

namespace GeneratedLevelHistorySchurIndexBridgeSM7

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

def fromSM6a
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistorySchurIndexBridgeSM7 Cell p A P wp W E K T M S H G where
  sourceSM6Witness := B.sourceSM6Witness
  witnessAt := B.witnessAt
  witnessAt_source_eq_SM6 := by
    intro k
    exact B.witnessAt_source_eq_SM6 k
  witnessAt_boundaryCarrier_eq_generated := by
    intro k
    exact (B.witnessAt k).boundaryCarrier_eq_generated
  toBoundaryIndex := B.toBoundaryIndex
  toBoundaryIndex_sourceStatus :=
    SM7GeneratedIndexMapSourceStatus.generatedHistoryToBoundaryMapSourceRequired
  toBoundaryIndex_sourceStatus_eq := by
    rfl
  toBoundaryIndex_level_eq_cutoff := by
    intro k
    exact B.toBoundaryIndex_level_eq_cutoff k
  boundaryOperator_from_SM6 := by
    exact B.boundaryOperator_from_SM6
  boundaryOperator_from_schur := by
    exact B.boundaryOperator_from_schur
  noFreeFintypeEnumerationStatus := SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7
  noFreeFintypeEnumerationStatus_eq := by
    rfl
  noLevelHistoryMatrixStatus := SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7
  noLevelHistoryMatrixStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7
  noCharpolyDiscriminantStatus_eq := by
    rfl

theorem fromSM6a_sourceSM6Witness
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    (fromSM6a B).sourceSM6Witness = B.sourceSM6Witness := by
  rfl

theorem fromSM6a_witnessAt_source_eq_SM6
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G)
    (k : GeneratedLevelHistoryIndexSM6 (fromSM6a B).sourceSM6Witness.level) :
    ((fromSM6a B).witnessAt k).sourceSM5Ledger =
      (fromSM6a B).sourceSM6Witness.sourceSM5Ledger :=
  (fromSM6a B).witnessAt_source_eq_SM6 k

theorem fromSM6a_witnessAt_boundaryCarrier_eq_generated
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G)
    (k : GeneratedLevelHistoryIndexSM6 (fromSM6a B).sourceSM6Witness.level) :
    ((fromSM6a B).witnessAt k).boundaryCarrier = GeneratedBoundaryIndex A :=
  (fromSM6a B).witnessAt_boundaryCarrier_eq_generated k

theorem fromSM6a_toBoundaryIndex_level_eq_cutoff
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G)
    (k : GeneratedLevelHistoryIndexSM6 (fromSM6a B).sourceSM6Witness.level) :
    (GeneratedBoundaryIndex.level ((fromSM6a B).toBoundaryIndex k)).val = p.L_max :=
  (fromSM6a B).toBoundaryIndex_level_eq_cutoff k

theorem fromSM6a_boundaryOperator_from_SM6
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    (fromSM6a B).sourceSM6Witness.boundaryOperator =
      (fromSM6a B).sourceSM6Witness.source.boundaryOperator :=
  (fromSM6a B).boundaryOperator_from_SM6

theorem fromSM6a_boundaryOperator_from_schur
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    (fromSM6a B).sourceSM6Witness.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          (fromSM6a B).sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  (fromSM6a B).boundaryOperator_from_schur

theorem fromSM6a_noLevelHistoryMatrix
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    (fromSM6a B).noLevelHistoryMatrixStatus =
      SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7 :=
  (fromSM6a B).noLevelHistoryMatrixStatus_eq

end GeneratedLevelHistorySchurIndexBridgeSM7

def regularGeneratedLevelHistorySchurIndexBridge_from_SM6a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistorySchurIndexBridgeSM7
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistorySchurIndexBridgeSM7.fromSM6a L.regularSource

def variableGeneratedLevelHistorySchurIndexBridge_from_SM6a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistorySchurIndexBridgeSM7
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistorySchurIndexBridgeSM7.fromSM6a L.variableSource

structure SM7BridgeRecheckLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM6aLedger : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight
  historicalSM7Gate : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight
  historicalSM7Gate_eq :
    historicalSM7Gate = sm7GeneratedLevelHistoryToSchurIndexGate sourceSM6aLedger.sourceSM6Ledger
  historicalRegularOutcome_eq_obstruction :
    historicalSM7Gate.regularOutcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
  historicalVariableOutcome_eq_obstruction :
    historicalSM7Gate.variableOutcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
  regularBridge :
    GeneratedLevelHistorySchurIndexBridgeSM7
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableBridge :
    GeneratedLevelHistorySchurIndexBridgeSM7
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularBridge_eq_from_SM6a :
    regularBridge = regularGeneratedLevelHistorySchurIndexBridge_from_SM6a sourceSM6aLedger
  variableBridge_eq_from_SM6a :
    variableBridge = variableGeneratedLevelHistorySchurIndexBridge_from_SM6a sourceSM6aLedger
  regularSourceStatus : SM7BridgeRecheckSourceStatus
  regularSourceStatus_eq :
    regularSourceStatus = SM7BridgeRecheckSourceStatus.consumedSM6aBoundaryPortSource
  variableSourceStatus : SM7BridgeRecheckSourceStatus
  variableSourceStatus_eq :
    variableSourceStatus = SM7BridgeRecheckSourceStatus.consumedSM6aBoundaryPortSource
  regularOutcome : SM7BridgeOutcome
  regularOutcome_eq : regularOutcome = SM7BridgeOutcome.bridgeSuccess
  variableOutcome : SM7BridgeOutcome
  variableOutcome_eq : variableOutcome = SM7BridgeOutcome.bridgeSuccess
  noFreeFintypeEnumerationStatus : SM7NoFreeFintypeEnumerationStatus
  noFreeFintypeEnumerationStatus_eq :
    noFreeFintypeEnumerationStatus =
      SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7
  noFreeReplacementIndexStatus : SM7NoFreeReplacementIndexStatus
  noFreeReplacementIndexStatus_eq :
    noFreeReplacementIndexStatus = SM7NoFreeReplacementIndexStatus.noFreeReplacementIndexInSM7
  noLevelHistoryMatrixStatus : SM7NoLevelHistoryMatrixStatus
  noLevelHistoryMatrixStatus_eq :
    noLevelHistoryMatrixStatus = SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7
  noCharpolyDiscriminantStatus : SM7NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7
  sm8GateStatus : SM7BridgeRecheckSM8GateStatus
  sm8GateStatus_eq :
    sm8GateStatus =
      SM7BridgeRecheckSM8GateStatus.sm8ReleasedAfterRegularVariableBridgeSuccess

def sm7BridgeRecheckLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    SM7BridgeRecheckLedger b β p regularWeight variableWeight where
  sourceSM6aLedger := L
  historicalSM7Gate := sm7GeneratedLevelHistoryToSchurIndexGate L.sourceSM6Ledger
  historicalSM7Gate_eq := by
    rfl
  historicalRegularOutcome_eq_obstruction := by
    rfl
  historicalVariableOutcome_eq_obstruction := by
    rfl
  regularBridge := regularGeneratedLevelHistorySchurIndexBridge_from_SM6a L
  variableBridge := variableGeneratedLevelHistorySchurIndexBridge_from_SM6a L
  regularBridge_eq_from_SM6a := by
    rfl
  variableBridge_eq_from_SM6a := by
    rfl
  regularSourceStatus := SM7BridgeRecheckSourceStatus.consumedSM6aBoundaryPortSource
  regularSourceStatus_eq := by
    rfl
  variableSourceStatus := SM7BridgeRecheckSourceStatus.consumedSM6aBoundaryPortSource
  variableSourceStatus_eq := by
    rfl
  regularOutcome := SM7BridgeOutcome.bridgeSuccess
  regularOutcome_eq := by
    rfl
  variableOutcome := SM7BridgeOutcome.bridgeSuccess
  variableOutcome_eq := by
    rfl
  noFreeFintypeEnumerationStatus := SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7
  noFreeFintypeEnumerationStatus_eq := by
    rfl
  noFreeReplacementIndexStatus := SM7NoFreeReplacementIndexStatus.noFreeReplacementIndexInSM7
  noFreeReplacementIndexStatus_eq := by
    rfl
  noLevelHistoryMatrixStatus := SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7
  noLevelHistoryMatrixStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7
  noCharpolyDiscriminantStatus_eq := by
    rfl
  sm8GateStatus := SM7BridgeRecheckSM8GateStatus.sm8ReleasedAfterRegularVariableBridgeSuccess
  sm8GateStatus_eq := by
    rfl

def sm7BridgeRecheckLedger_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM7BridgeRecheckLedger b β p regularWeight variableWeight :=
  sm7BridgeRecheckLedger
    (sm6aGeneratedLevelHistoryBoundaryPortSourceLedger_from_SM5 L level levelIndex)

theorem sm7BridgeRecheck_regular_outcome
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.regularOutcome = SM7BridgeOutcome.bridgeSuccess :=
  L.regularOutcome_eq

theorem sm7BridgeRecheck_variable_outcome
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.variableOutcome = SM7BridgeOutcome.bridgeSuccess :=
  L.variableOutcome_eq

theorem sm7BridgeRecheck_historical_regular_outcome_is_obstruction
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.historicalSM7Gate.regularOutcome =
      SM7BridgeOutcome.obstructionMissingGeneratedIndexSource :=
  L.historicalRegularOutcome_eq_obstruction

theorem sm7BridgeRecheck_historical_variable_outcome_is_obstruction
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.historicalSM7Gate.variableOutcome =
      SM7BridgeOutcome.obstructionMissingGeneratedIndexSource :=
  L.historicalVariableOutcome_eq_obstruction

theorem sm7BridgeRecheck_regularBridge_from_SM6a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.regularBridge = regularGeneratedLevelHistorySchurIndexBridge_from_SM6a L.sourceSM6aLedger :=
  L.regularBridge_eq_from_SM6a

theorem sm7BridgeRecheck_variableBridge_from_SM6a
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.variableBridge = variableGeneratedLevelHistorySchurIndexBridge_from_SM6a L.sourceSM6aLedger :=
  L.variableBridge_eq_from_SM6a

theorem sm7BridgeRecheck_sm8_gate_released
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.sm8GateStatus =
      SM7BridgeRecheckSM8GateStatus.sm8ReleasedAfterRegularVariableBridgeSuccess :=
  L.sm8GateStatus_eq

theorem sm7BridgeRecheck_noLevelHistoryMatrix
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.noLevelHistoryMatrixStatus = SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7 :=
  L.noLevelHistoryMatrixStatus_eq

theorem sm7BridgeRecheck_noCharpolyDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM7BridgeRecheckLedger b β p regularWeight variableWeight) :
    L.noCharpolyDiscriminantStatus =
      SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7 :=
  L.noCharpolyDiscriminantStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
