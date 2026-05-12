import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM7BridgeOutcome where
  | bridgeSuccess
  | obstructionMissingGeneratedIndexSource
  deriving DecidableEq, Repr

inductive SM7GeneratedIndexMapSourceStatus where
  | generatedHistoryToBoundaryMapSourceRequired
  deriving DecidableEq, Repr

inductive SM7MissingLevelToBoundaryMapSourceStatus where
  | missingGeneratedLevelHistoryToBoundaryMapSource
  deriving DecidableEq, Repr

inductive SM7MissingSchurIndexProvenanceStatus where
  | missingGeneratedSchurIndexProvenance
  deriving DecidableEq, Repr

inductive SM7NoFreeFintypeEnumerationStatus where
  | noFreeFintypeEnumerationInSM7
  deriving DecidableEq, Repr

inductive SM7NoFreeReplacementIndexStatus where
  | noFreeReplacementIndexInSM7
  deriving DecidableEq, Repr

inductive SM7NoLevelHistoryMatrixStatus where
  | noLevelHistoryMatrixInSM7
  deriving DecidableEq, Repr

inductive SM7NoCharpolyDiscriminantStatus where
  | noCharpolyFactorDiscriminantDataInSM7
  deriving DecidableEq, Repr

inductive SM7NextPhaseBlockedStatus where
  | sm8BlockedUntilBridgeSuccess
  deriving DecidableEq, Repr

structure GeneratedLevelHistorySchurIndexBridgeSM7
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
  sourceSM6Witness : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G
  witnessAt : (k : GeneratedLevelHistoryIndexSM6 sourceSM6Witness.level) →
    GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G
  witnessAt_source_eq_SM6 : ∀ k, (witnessAt k).sourceSM5Ledger = sourceSM6Witness.sourceSM5Ledger
  witnessAt_boundaryCarrier_eq_generated : ∀ k,
    (witnessAt k).boundaryCarrier = GeneratedBoundaryIndex A
  toBoundaryIndex : GeneratedLevelHistoryIndexSM6 sourceSM6Witness.level → GeneratedBoundaryIndex A
  toBoundaryIndex_sourceStatus : SM7GeneratedIndexMapSourceStatus
  toBoundaryIndex_sourceStatus_eq :
    toBoundaryIndex_sourceStatus =
      SM7GeneratedIndexMapSourceStatus.generatedHistoryToBoundaryMapSourceRequired
  toBoundaryIndex_level_eq_cutoff : ∀ k,
    (GeneratedBoundaryIndex.level (toBoundaryIndex k)).val = p.L_max
  boundaryOperator_from_SM6 :
    sourceSM6Witness.boundaryOperator = sourceSM6Witness.source.boundaryOperator
  boundaryOperator_from_schur :
    sourceSM6Witness.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  noFreeFintypeEnumerationStatus : SM7NoFreeFintypeEnumerationStatus
  noFreeFintypeEnumerationStatus_eq :
    noFreeFintypeEnumerationStatus =
      SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7
  noLevelHistoryMatrixStatus : SM7NoLevelHistoryMatrixStatus
  noLevelHistoryMatrixStatus_eq :
    noLevelHistoryMatrixStatus = SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7
  noCharpolyDiscriminantStatus : SM7NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7

structure GeneratedLevelHistorySchurIndexObstructionSM7
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
  sourceSM6Witness : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G
  witnessAt : (k : GeneratedLevelHistoryIndexSM6 sourceSM6Witness.level) →
    GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G
  witnessAt_source_eq_SM5 : ∀ k,
    (witnessAt k).source = sourceSM6Witness.sourceSM5Ledger
  witnessAt_boundaryCarrier_eq_generated : ∀ k,
    (witnessAt k).boundaryCarrier = GeneratedBoundaryIndex A
  witnessAt_boundaryOperator_eq_SM5 : ∀ k,
    (witnessAt k).boundaryOperator = (witnessAt k).source.boundaryOperator
  witnessAt_boundaryOperator_eq_schur : ∀ k,
    (witnessAt k).boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          (witnessAt k).source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  witnessAt_apply_eq_mulVec : ∀ k (φ : GeneratedBoundaryIndex A → ℝ),
    (witnessAt k).«apply» φ = (witnessAt k).boundaryOperator.mulVec φ
  outcome : SM7BridgeOutcome
  outcome_eq_obstruction : outcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
  missingLevelToBoundaryMapSource : SM7MissingLevelToBoundaryMapSourceStatus
  missingLevelToBoundaryMapSource_eq :
    missingLevelToBoundaryMapSource =
      SM7MissingLevelToBoundaryMapSourceStatus.missingGeneratedLevelHistoryToBoundaryMapSource
  missingSchurIndexProvenance : SM7MissingSchurIndexProvenanceStatus
  missingSchurIndexProvenance_eq :
    missingSchurIndexProvenance =
      SM7MissingSchurIndexProvenanceStatus.missingGeneratedSchurIndexProvenance
  noFreeFintypeEnumerationStatus : SM7NoFreeFintypeEnumerationStatus
  noFreeFintypeEnumerationStatus_eq :
    noFreeFintypeEnumerationStatus =
      SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7
  noFreeReplacementIndexStatus : SM7NoFreeReplacementIndexStatus
  noFreeReplacementIndexStatus_eq :
    noFreeReplacementIndexStatus =
      SM7NoFreeReplacementIndexStatus.noFreeReplacementIndexInSM7
  noLevelHistoryMatrixStatus : SM7NoLevelHistoryMatrixStatus
  noLevelHistoryMatrixStatus_eq :
    noLevelHistoryMatrixStatus = SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7
  noCharpolyDiscriminantStatus : SM7NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7
  nextPhaseBlockedStatus : SM7NextPhaseBlockedStatus
  nextPhaseBlockedStatus_eq :
    nextPhaseBlockedStatus = SM7NextPhaseBlockedStatus.sm8BlockedUntilBridgeSuccess

namespace GeneratedLevelHistorySchurIndexObstructionSM7

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

def fromSM6Witness
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G where
  sourceSM6Witness := W6
  witnessAt := fun k => GeneratedLevelStepWitnessSM6.fromSM5 W6.sourceSM5Ledger W6.level k
  witnessAt_source_eq_SM5 := by
    intro k
    rfl
  witnessAt_boundaryCarrier_eq_generated := by
    intro k
    rfl
  witnessAt_boundaryOperator_eq_SM5 := by
    intro k
    rfl
  witnessAt_boundaryOperator_eq_schur := by
    intro k
    exact (GeneratedLevelStepWitnessSM6.fromSM5 W6.sourceSM5Ledger W6.level k).boundaryOperator_eq_schur
  witnessAt_apply_eq_mulVec := by
    intro k φ
    exact (GeneratedLevelStepWitnessSM6.fromSM5 W6.sourceSM5Ledger W6.level k).apply_eq_mulVec φ
  outcome := SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
  outcome_eq_obstruction := by
    rfl
  missingLevelToBoundaryMapSource :=
    SM7MissingLevelToBoundaryMapSourceStatus.missingGeneratedLevelHistoryToBoundaryMapSource
  missingLevelToBoundaryMapSource_eq := by
    rfl
  missingSchurIndexProvenance :=
    SM7MissingSchurIndexProvenanceStatus.missingGeneratedSchurIndexProvenance
  missingSchurIndexProvenance_eq := by
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
  nextPhaseBlockedStatus := SM7NextPhaseBlockedStatus.sm8BlockedUntilBridgeSuccess
  nextPhaseBlockedStatus_eq := by
    rfl

theorem outcome_is_obstruction
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.outcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource :=
  O.outcome_eq_obstruction

theorem missingLevelToBoundaryMapSource_is_recorded
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.missingLevelToBoundaryMapSource =
      SM7MissingLevelToBoundaryMapSourceStatus.missingGeneratedLevelHistoryToBoundaryMapSource :=
  O.missingLevelToBoundaryMapSource_eq

theorem missingSchurIndexProvenance_is_recorded
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.missingSchurIndexProvenance =
      SM7MissingSchurIndexProvenanceStatus.missingGeneratedSchurIndexProvenance :=
  O.missingSchurIndexProvenance_eq

theorem noFreeFintypeEnumeration_for_obstruction
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.noFreeFintypeEnumerationStatus =
      SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7 :=
  O.noFreeFintypeEnumerationStatus_eq

theorem noFreeReplacementIndex_for_obstruction
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.noFreeReplacementIndexStatus =
      SM7NoFreeReplacementIndexStatus.noFreeReplacementIndexInSM7 :=
  O.noFreeReplacementIndexStatus_eq

theorem noLevelHistoryMatrix_for_obstruction
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.noLevelHistoryMatrixStatus = SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7 :=
  O.noLevelHistoryMatrixStatus_eq

theorem noCharpolyDiscriminant_for_obstruction
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.noCharpolyDiscriminantStatus =
      SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7 :=
  O.noCharpolyDiscriminantStatus_eq

theorem sm8_blocked_for_obstruction
    (O : GeneratedLevelHistorySchurIndexObstructionSM7 Cell p A P wp W E K T M S H G) :
    O.nextPhaseBlockedStatus = SM7NextPhaseBlockedStatus.sm8BlockedUntilBridgeSuccess :=
  O.nextPhaseBlockedStatus_eq

end GeneratedLevelHistorySchurIndexObstructionSM7

structure SM7GeneratedLevelHistoryToSchurIndexGate
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM6Ledger : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight
  level : Nat
  level_eq_SM6 : level = sourceSM6Ledger.level
  regularWitnessAt : (k : GeneratedLevelHistoryIndexSM6 sourceSM6Ledger.level) →
    GeneratedLevelStepWitnessSM6
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableWitnessAt : (k : GeneratedLevelHistoryIndexSM6 sourceSM6Ledger.level) →
    GeneratedLevelStepWitnessSM6
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularWitnessAt_eq_from_SM5 : ∀ k,
    regularWitnessAt k =
      regularGeneratedLevelStepWitness_from_SM5 sourceSM6Ledger.sourceSM5Ledger
        sourceSM6Ledger.level k
  variableWitnessAt_eq_from_SM5 : ∀ k,
    variableWitnessAt k =
      variableGeneratedLevelStepWitness_from_SM5 sourceSM6Ledger.sourceSM5Ledger
        sourceSM6Ledger.level k
  regularObstruction :
    GeneratedLevelHistorySchurIndexObstructionSM7
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableObstruction :
    GeneratedLevelHistorySchurIndexObstructionSM7
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularOutcome : SM7BridgeOutcome
  regularOutcome_eq : regularOutcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
  variableOutcome : SM7BridgeOutcome
  variableOutcome_eq : variableOutcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
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
  nextPhaseBlockedStatus : SM7NextPhaseBlockedStatus
  nextPhaseBlockedStatus_eq :
    nextPhaseBlockedStatus = SM7NextPhaseBlockedStatus.sm8BlockedUntilBridgeSuccess

def sm7GeneratedLevelHistoryToSchurIndexGate
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight where
  sourceSM6Ledger := L
  level := L.level
  level_eq_SM6 := by
    rfl
  regularWitnessAt := fun k =>
    regularGeneratedLevelStepWitness_from_SM5 L.sourceSM5Ledger L.level k
  variableWitnessAt := fun k =>
    variableGeneratedLevelStepWitness_from_SM5 L.sourceSM5Ledger L.level k
  regularWitnessAt_eq_from_SM5 := by
    intro k
    rfl
  variableWitnessAt_eq_from_SM5 := by
    intro k
    rfl
  regularObstruction :=
    GeneratedLevelHistorySchurIndexObstructionSM7.fromSM6Witness L.regularWitness
  variableObstruction :=
    GeneratedLevelHistorySchurIndexObstructionSM7.fromSM6Witness L.variableWitness
  regularOutcome := SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
  regularOutcome_eq := by
    rfl
  variableOutcome := SM7BridgeOutcome.obstructionMissingGeneratedIndexSource
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
  nextPhaseBlockedStatus := SM7NextPhaseBlockedStatus.sm8BlockedUntilBridgeSuccess
  nextPhaseBlockedStatus_eq := by
    rfl

theorem sm7Gate_regular_outcome
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.regularOutcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource :=
  G7.regularOutcome_eq

theorem sm7Gate_variable_outcome
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.variableOutcome = SM7BridgeOutcome.obstructionMissingGeneratedIndexSource :=
  G7.variableOutcome_eq

theorem sm7Gate_noFreeFintypeEnumeration
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.noFreeFintypeEnumerationStatus =
      SM7NoFreeFintypeEnumerationStatus.noFreeFintypeEnumerationInSM7 :=
  G7.noFreeFintypeEnumerationStatus_eq

theorem sm7Gate_noFreeReplacementIndex
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.noFreeReplacementIndexStatus = SM7NoFreeReplacementIndexStatus.noFreeReplacementIndexInSM7 :=
  G7.noFreeReplacementIndexStatus_eq

theorem sm7Gate_noLevelHistoryMatrix
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.noLevelHistoryMatrixStatus = SM7NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM7 :=
  G7.noLevelHistoryMatrixStatus_eq

theorem sm7Gate_noCharpolyDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.noCharpolyDiscriminantStatus =
      SM7NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM7 :=
  G7.noCharpolyDiscriminantStatus_eq

theorem sm7Gate_sm8_blocked
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (G7 : SM7GeneratedLevelHistoryToSchurIndexGate b β p regularWeight variableWeight) :
    G7.nextPhaseBlockedStatus = SM7NextPhaseBlockedStatus.sm8BlockedUntilBridgeSuccess :=
  G7.nextPhaseBlockedStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
