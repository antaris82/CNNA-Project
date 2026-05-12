import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM6aBoundaryPortSourceStatus where
  | generatedBoundaryPortFromSM6Layer
  deriving DecidableEq, Repr

inductive SM6aBoundaryCarrierProvenanceStatus where
  | boundaryCarrierFromGeneratedBoundaryIndex
  deriving DecidableEq, Repr

inductive SM6aBoundaryOperatorProvenanceStatus where
  | boundaryOperatorReusedFromSM6SM5Schur
  deriving DecidableEq, Repr

inductive SM6aNoFreeEnumerationStatus where
  | noFreeEnumerationInSM6a
  deriving DecidableEq, Repr

inductive SM6aNoFreeTableStatus where
  | noFreeTableInSM6a
  deriving DecidableEq, Repr

inductive SM6aNoChoiceStatus where
  | noChoiceInSM6a
  deriving DecidableEq, Repr

inductive SM6aNoMatrixStartStatus where
  | noMatrixStartInSM6a
  deriving DecidableEq, Repr

inductive SM6aNoMatrixInvIntroducedStatus where
  | noMatrixInvIntroducedInSM6a
  deriving DecidableEq, Repr

inductive SM6aNoCharpolyDiscriminantStatus where
  | noCharpolyFactorDiscriminantDataInSM6a
  deriving DecidableEq, Repr

inductive SM6aNextConsumerStatus where
  | sm7BridgeRecheckRequiredBeforeSM8
  deriving DecidableEq, Repr

structure GeneratedLevelHistoryBoundaryPortSourceSM6a
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
  witnessAt_eq_from_SM5 : ∀ k,
    witnessAt k =
      GeneratedLevelStepWitnessSM6.fromSM5 sourceSM6Witness.sourceSM5Ledger
        sourceSM6Witness.level k
  witnessAt_source_eq_SM6 : ∀ k,
    (witnessAt k).sourceSM5Ledger = sourceSM6Witness.sourceSM5Ledger
  historyIndex : Type
  historyIndex_eq : historyIndex = GeneratedLevelHistoryIndexSM6 sourceSM6Witness.level
  historyIndex_source : GeneratedLevelHistoryIndexSM6 sourceSM6Witness.level
  historyIndex_source_eq_SM6 : historyIndex_source = sourceSM6Witness.levelIndex
  toBoundaryIndex : GeneratedLevelHistoryIndexSM6 sourceSM6Witness.level → GeneratedBoundaryIndex A
  toBoundaryIndex_sourceStatus : SM6aBoundaryPortSourceStatus
  toBoundaryIndex_sourceStatus_eq :
    toBoundaryIndex_sourceStatus =
      SM6aBoundaryPortSourceStatus.generatedBoundaryPortFromSM6Layer
  toBoundaryIndex_level_eq_cutoff : ∀ k,
    (GeneratedBoundaryIndex.level (toBoundaryIndex k)).val = p.L_max
  toBoundaryIndex_mem_boundaryCarrier : ∀ k,
    GeneratedBoundaryIndex.toApproximantIndex (toBoundaryIndex k) ∈ P.boundaryCarrier
  boundaryCarrierProvenanceStatus : SM6aBoundaryCarrierProvenanceStatus
  boundaryCarrierProvenanceStatus_eq :
    boundaryCarrierProvenanceStatus =
      SM6aBoundaryCarrierProvenanceStatus.boundaryCarrierFromGeneratedBoundaryIndex
  boundaryCarrier_eq_generated :
    sourceSM6Witness.boundaryCarrier = GeneratedBoundaryIndex A
  boundaryOperatorProvenanceStatus : SM6aBoundaryOperatorProvenanceStatus
  boundaryOperatorProvenanceStatus_eq :
    boundaryOperatorProvenanceStatus =
      SM6aBoundaryOperatorProvenanceStatus.boundaryOperatorReusedFromSM6SM5Schur
  boundaryOperator_from_SM6 :
    sourceSM6Witness.boundaryOperator = sourceSM6Witness.source.boundaryOperator
  boundaryOperator_from_schur :
    sourceSM6Witness.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  apply_from_SM6 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM6Witness.«apply» φ = sourceSM6Witness.source.«apply» φ
  apply_from_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM6Witness.«apply» φ = sourceSM6Witness.boundaryOperator.mulVec φ
  noFreeEnumerationStatus : SM6aNoFreeEnumerationStatus
  noFreeEnumerationStatus_eq :
    noFreeEnumerationStatus = SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a
  noFreeTableStatus : SM6aNoFreeTableStatus
  noFreeTableStatus_eq :
    noFreeTableStatus = SM6aNoFreeTableStatus.noFreeTableInSM6a
  noChoiceStatus : SM6aNoChoiceStatus
  noChoiceStatus_eq :
    noChoiceStatus = SM6aNoChoiceStatus.noChoiceInSM6a
  noMatrixStartStatus : SM6aNoMatrixStartStatus
  noMatrixStartStatus_eq :
    noMatrixStartStatus = SM6aNoMatrixStartStatus.noMatrixStartInSM6a
  noMatrixInvIntroducedStatus : SM6aNoMatrixInvIntroducedStatus
  noMatrixInvIntroducedStatus_eq :
    noMatrixInvIntroducedStatus =
      SM6aNoMatrixInvIntroducedStatus.noMatrixInvIntroducedInSM6a
  noCharpolyDiscriminantStatus : SM6aNoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM6aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6a
  nextConsumerStatus : SM6aNextConsumerStatus
  nextConsumerStatus_eq :
    nextConsumerStatus = SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8

namespace GeneratedLevelHistoryBoundaryPortSourceSM6a

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

def fromBoundaryMap
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G)
    (toBoundaryIndex : GeneratedLevelHistoryIndexSM6 W6.level → GeneratedBoundaryIndex A)
    (toBoundaryIndex_level_eq_cutoff : ∀ k,
      (GeneratedBoundaryIndex.level (toBoundaryIndex k)).val = p.L_max) :
    GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G where
  sourceSM6Witness := W6
  witnessAt := fun k => GeneratedLevelStepWitnessSM6.fromSM5 W6.sourceSM5Ledger W6.level k
  witnessAt_eq_from_SM5 := by
    intro k
    rfl
  witnessAt_source_eq_SM6 := by
    intro k
    rfl
  historyIndex := GeneratedLevelHistoryIndexSM6 W6.level
  historyIndex_eq := by
    rfl
  historyIndex_source := W6.levelIndex
  historyIndex_source_eq_SM6 := by
    rfl
  toBoundaryIndex := toBoundaryIndex
  toBoundaryIndex_sourceStatus := SM6aBoundaryPortSourceStatus.generatedBoundaryPortFromSM6Layer
  toBoundaryIndex_sourceStatus_eq := by
    rfl
  toBoundaryIndex_level_eq_cutoff := toBoundaryIndex_level_eq_cutoff
  toBoundaryIndex_mem_boundaryCarrier := by
    intro k
    rw [P.boundaryCarrier_eq]
    exact boundary_mem_boundaryCarrier (toBoundaryIndex k)
  boundaryCarrierProvenanceStatus :=
    SM6aBoundaryCarrierProvenanceStatus.boundaryCarrierFromGeneratedBoundaryIndex
  boundaryCarrierProvenanceStatus_eq := by
    rfl
  boundaryCarrier_eq_generated := by
    exact W6.boundaryCarrier_eq_generated
  boundaryOperatorProvenanceStatus :=
    SM6aBoundaryOperatorProvenanceStatus.boundaryOperatorReusedFromSM6SM5Schur
  boundaryOperatorProvenanceStatus_eq := by
    rfl
  boundaryOperator_from_SM6 := by
    exact W6.boundaryOperator_eq_SM5
  boundaryOperator_from_schur := by
    exact W6.boundaryOperator_eq_schur
  apply_from_SM6 := by
    intro φ
    exact W6.apply_eq_SM5 φ
  apply_from_mulVec := by
    intro φ
    exact W6.apply_eq_mulVec φ
  noFreeEnumerationStatus := SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a
  noFreeEnumerationStatus_eq := by
    rfl
  noFreeTableStatus := SM6aNoFreeTableStatus.noFreeTableInSM6a
  noFreeTableStatus_eq := by
    rfl
  noChoiceStatus := SM6aNoChoiceStatus.noChoiceInSM6a
  noChoiceStatus_eq := by
    rfl
  noMatrixStartStatus := SM6aNoMatrixStartStatus.noMatrixStartInSM6a
  noMatrixStartStatus_eq := by
    rfl
  noMatrixInvIntroducedStatus :=
    SM6aNoMatrixInvIntroducedStatus.noMatrixInvIntroducedInSM6a
  noMatrixInvIntroducedStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM6aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6a
  noCharpolyDiscriminantStatus_eq := by
    rfl
  nextConsumerStatus := SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8
  nextConsumerStatus_eq := by
    rfl

theorem toBoundaryIndex_level
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G)
    (k : GeneratedLevelHistoryIndexSM6 B.sourceSM6Witness.level) :
    (GeneratedBoundaryIndex.level (B.toBoundaryIndex k)).val = p.L_max :=
  B.toBoundaryIndex_level_eq_cutoff k

theorem toBoundaryIndex_mem_boundaryCarrier_proof
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G)
    (k : GeneratedLevelHistoryIndexSM6 B.sourceSM6Witness.level) :
    GeneratedBoundaryIndex.toApproximantIndex (B.toBoundaryIndex k) ∈ P.boundaryCarrier :=
  B.toBoundaryIndex_mem_boundaryCarrier k

theorem boundaryCarrier_from_SM6
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.sourceSM6Witness.boundaryCarrier = GeneratedBoundaryIndex A :=
  B.boundaryCarrier_eq_generated

theorem boundaryOperator_from_SM6_proof
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.sourceSM6Witness.boundaryOperator = B.sourceSM6Witness.source.boundaryOperator :=
  B.boundaryOperator_from_SM6

theorem boundaryOperator_from_schur_proof
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.sourceSM6Witness.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          B.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  B.boundaryOperator_from_schur

theorem apply_from_mulVec_proof
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    B.sourceSM6Witness.«apply» φ = B.sourceSM6Witness.boundaryOperator.mulVec φ :=
  B.apply_from_mulVec φ

theorem noFreeEnumeration
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.noFreeEnumerationStatus = SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a :=
  B.noFreeEnumerationStatus_eq

theorem noFreeTable
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.noFreeTableStatus = SM6aNoFreeTableStatus.noFreeTableInSM6a :=
  B.noFreeTableStatus_eq

theorem noChoice
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.noChoiceStatus = SM6aNoChoiceStatus.noChoiceInSM6a :=
  B.noChoiceStatus_eq

theorem noMatrixStart
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.noMatrixStartStatus = SM6aNoMatrixStartStatus.noMatrixStartInSM6a :=
  B.noMatrixStartStatus_eq

theorem noMatrixInvIntroduced
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.noMatrixInvIntroducedStatus =
      SM6aNoMatrixInvIntroducedStatus.noMatrixInvIntroducedInSM6a :=
  B.noMatrixInvIntroducedStatus_eq

theorem noCharpolyDiscriminant
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.noCharpolyDiscriminantStatus =
      SM6aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6a :=
  B.noCharpolyDiscriminantStatus_eq

theorem nextConsumer_is_SM7Recheck
    (B : GeneratedLevelHistoryBoundaryPortSourceSM6a Cell p A P wp W E K T M S H G) :
    B.nextConsumerStatus = SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8 :=
  B.nextConsumerStatus_eq

end GeneratedLevelHistoryBoundaryPortSourceSM6a

def regularGeneratedBoundaryZeroPortSM6a
    (b : Nat) (p : ConcretePolicyOf) :
    GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) := by
  let level : Fin (p.L_max + 1) := ⟨p.L_max, Nat.lt_succ_self p.L_max⟩
  have hmem : ConcreteSubstrate.zeroCell b p.L_max ∈
      (regularGeneratedApproximantStrong b p).approximant.carrier p.L_max := by
    rw [regularGeneratedApproximantStrong_carrier_eq_univ_of_le b (p := p) le_rfl]
    exact Finset.mem_univ _
  exact
    ⟨⟨level, ⟨ConcreteSubstrate.zeroCell b p.L_max, hmem⟩⟩, by
      rfl⟩

def variableGeneratedBoundaryZeroPortSM6a
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) := by
  let level : Fin (p.L_max + 1) := ⟨p.L_max, Nat.lt_succ_self p.L_max⟩
  have hmem : LevelVariableSubstrate.zeroCell β p.L_max ∈
      (variableGeneratedApproximantStrong β p).approximant.carrier p.L_max := by
    rw [variableGeneratedApproximantStrong_carrier_eq_univ_of_le β (p := p) le_rfl]
    exact Finset.mem_univ _
  exact
    ⟨⟨level, ⟨LevelVariableSubstrate.zeroCell β p.L_max, hmem⟩⟩, by
      rfl⟩

theorem regularGeneratedBoundaryZeroPortSM6a_level_eq_cutoff
    (b : Nat) (p : ConcretePolicyOf) :
    (GeneratedBoundaryIndex.level (regularGeneratedBoundaryZeroPortSM6a b p)).val = p.L_max :=
  GeneratedBoundaryIndex.level_eq_cutoff (regularGeneratedBoundaryZeroPortSM6a b p)

theorem variableGeneratedBoundaryZeroPortSM6a_level_eq_cutoff
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (GeneratedBoundaryIndex.level (variableGeneratedBoundaryZeroPortSM6a β p)).val = p.L_max :=
  GeneratedBoundaryIndex.level_eq_cutoff (variableGeneratedBoundaryZeroPortSM6a β p)

def regularGeneratedLevelHistoryBoundaryPortSource_from_SM6
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryBoundaryPortSourceSM6a
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryBoundaryPortSourceSM6a.fromBoundaryMap L.regularWitness
    (fun _ => regularGeneratedBoundaryZeroPortSM6a b p)
    (fun _ => regularGeneratedBoundaryZeroPortSM6a_level_eq_cutoff b p)

def variableGeneratedLevelHistoryBoundaryPortSource_from_SM6
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    GeneratedLevelHistoryBoundaryPortSourceSM6a
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryBoundaryPortSourceSM6a.fromBoundaryMap L.variableWitness
    (fun _ => variableGeneratedBoundaryZeroPortSM6a β p)
    (fun _ => variableGeneratedBoundaryZeroPortSM6a_level_eq_cutoff β p)

structure SM6aGeneratedLevelHistoryBoundaryPortSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM6Ledger : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedLevelHistoryBoundaryPortSourceSM6a
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
  variableSource :
    GeneratedLevelHistoryBoundaryPortSourceSM6a
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
  regularSource_eq_from_SM6 :
    regularSource = regularGeneratedLevelHistoryBoundaryPortSource_from_SM6 sourceSM6Ledger
  variableSource_eq_from_SM6 :
    variableSource = variableGeneratedLevelHistoryBoundaryPortSource_from_SM6 sourceSM6Ledger
  regular_sourceSM6Witness_eq : regularSource.sourceSM6Witness = sourceSM6Ledger.regularWitness
  variable_sourceSM6Witness_eq : variableSource.sourceSM6Witness = sourceSM6Ledger.variableWitness
  regular_toBoundaryIndex_level_eq_cutoff :
    ∀ k : GeneratedLevelHistoryIndexSM6 regularSource.sourceSM6Witness.level,
      (GeneratedBoundaryIndex.level (regularSource.toBoundaryIndex k)).val = p.L_max
  variable_toBoundaryIndex_level_eq_cutoff :
    ∀ k : GeneratedLevelHistoryIndexSM6 variableSource.sourceSM6Witness.level,
      (GeneratedBoundaryIndex.level (variableSource.toBoundaryIndex k)).val = p.L_max
  regular_toBoundaryIndex_mem_boundaryCarrier :
    ∀ k : GeneratedLevelHistoryIndexSM6 regularSource.sourceSM6Witness.level,
      GeneratedBoundaryIndex.toApproximantIndex (regularSource.toBoundaryIndex k) ∈
      (regularGeneratedBoundaryInteriorPartition b p).boundaryCarrier
  variable_toBoundaryIndex_mem_boundaryCarrier :
    ∀ k : GeneratedLevelHistoryIndexSM6 variableSource.sourceSM6Witness.level,
      GeneratedBoundaryIndex.toApproximantIndex (variableSource.toBoundaryIndex k) ∈
      (variableGeneratedBoundaryInteriorPartition β p).boundaryCarrier
  regular_boundaryOperator_from_SM6 :
    regularSource.sourceSM6Witness.boundaryOperator =
      regularSource.sourceSM6Witness.source.boundaryOperator
  variable_boundaryOperator_from_SM6 :
    variableSource.sourceSM6Witness.boundaryOperator =
      variableSource.sourceSM6Witness.source.boundaryOperator
  regular_apply_from_mulVec :
    ∀ φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ,
      regularSource.sourceSM6Witness.«apply» φ =
        regularSource.sourceSM6Witness.boundaryOperator.mulVec φ
  variable_apply_from_mulVec :
    ∀ φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ,
      variableSource.sourceSM6Witness.«apply» φ =
        variableSource.sourceSM6Witness.boundaryOperator.mulVec φ
  regularNoFreeEnumeration :
    regularSource.noFreeEnumerationStatus = SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a
  variableNoFreeEnumeration :
    variableSource.noFreeEnumerationStatus = SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a
  regularNoFreeTable :
    regularSource.noFreeTableStatus = SM6aNoFreeTableStatus.noFreeTableInSM6a
  variableNoFreeTable :
    variableSource.noFreeTableStatus = SM6aNoFreeTableStatus.noFreeTableInSM6a
  regularNoChoice :
    regularSource.noChoiceStatus = SM6aNoChoiceStatus.noChoiceInSM6a
  variableNoChoice :
    variableSource.noChoiceStatus = SM6aNoChoiceStatus.noChoiceInSM6a
  regularNoMatrixStart :
    regularSource.noMatrixStartStatus = SM6aNoMatrixStartStatus.noMatrixStartInSM6a
  variableNoMatrixStart :
    variableSource.noMatrixStartStatus = SM6aNoMatrixStartStatus.noMatrixStartInSM6a
  regularNoMatrixInvIntroduced :
    regularSource.noMatrixInvIntroducedStatus =
      SM6aNoMatrixInvIntroducedStatus.noMatrixInvIntroducedInSM6a
  variableNoMatrixInvIntroduced :
    variableSource.noMatrixInvIntroducedStatus =
      SM6aNoMatrixInvIntroducedStatus.noMatrixInvIntroducedInSM6a
  regularNoCharpolyDiscriminant :
    regularSource.noCharpolyDiscriminantStatus =
      SM6aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6a
  variableNoCharpolyDiscriminant :
    variableSource.noCharpolyDiscriminantStatus =
      SM6aNoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6a
  regularNextConsumerStatus :
    regularSource.nextConsumerStatus = SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8
  variableNextConsumerStatus :
    variableSource.nextConsumerStatus = SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8

def sm6aGeneratedLevelHistoryBoundaryPortSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight where
  sourceSM6Ledger := L
  regularSource := regularGeneratedLevelHistoryBoundaryPortSource_from_SM6 L
  variableSource := variableGeneratedLevelHistoryBoundaryPortSource_from_SM6 L
  regularSource_eq_from_SM6 := by
    rfl
  variableSource_eq_from_SM6 := by
    rfl
  regular_sourceSM6Witness_eq := by
    rfl
  variable_sourceSM6Witness_eq := by
    rfl
  regular_toBoundaryIndex_level_eq_cutoff := by
    intro k
    exact (regularGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).toBoundaryIndex_level_eq_cutoff k
  variable_toBoundaryIndex_level_eq_cutoff := by
    intro k
    exact (variableGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).toBoundaryIndex_level_eq_cutoff k
  regular_toBoundaryIndex_mem_boundaryCarrier := by
    intro k
    exact (regularGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).toBoundaryIndex_mem_boundaryCarrier k
  variable_toBoundaryIndex_mem_boundaryCarrier := by
    intro k
    exact (variableGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).toBoundaryIndex_mem_boundaryCarrier k
  regular_boundaryOperator_from_SM6 := by
    exact (regularGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).boundaryOperator_from_SM6
  variable_boundaryOperator_from_SM6 := by
    exact (variableGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).boundaryOperator_from_SM6
  regular_apply_from_mulVec := by
    intro φ
    exact (regularGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).apply_from_mulVec φ
  variable_apply_from_mulVec := by
    intro φ
    exact (variableGeneratedLevelHistoryBoundaryPortSource_from_SM6 L).apply_from_mulVec φ
  regularNoFreeEnumeration := by
    rfl
  variableNoFreeEnumeration := by
    rfl
  regularNoFreeTable := by
    rfl
  variableNoFreeTable := by
    rfl
  regularNoChoice := by
    rfl
  variableNoChoice := by
    rfl
  regularNoMatrixStart := by
    rfl
  variableNoMatrixStart := by
    rfl
  regularNoMatrixInvIntroduced := by
    rfl
  variableNoMatrixInvIntroduced := by
    rfl
  regularNoCharpolyDiscriminant := by
    rfl
  variableNoCharpolyDiscriminant := by
    rfl
  regularNextConsumerStatus := by
    rfl
  variableNextConsumerStatus := by
    rfl

def sm6aGeneratedLevelHistoryBoundaryPortSourceLedger_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight :=
  sm6aGeneratedLevelHistoryBoundaryPortSourceLedger
    (sm6GeneratedLevelStepWitnessLedger L level levelIndex)

theorem sm6a_regular_toBoundaryIndex_level_eq_cutoff
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight)
    (k : GeneratedLevelHistoryIndexSM6 L.regularSource.sourceSM6Witness.level) :
    (GeneratedBoundaryIndex.level (L.regularSource.toBoundaryIndex k)).val = p.L_max :=
  L.regular_toBoundaryIndex_level_eq_cutoff k

theorem sm6a_variable_toBoundaryIndex_level_eq_cutoff
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight)
    (k : GeneratedLevelHistoryIndexSM6 L.variableSource.sourceSM6Witness.level) :
    (GeneratedBoundaryIndex.level (L.variableSource.toBoundaryIndex k)).val = p.L_max :=
  L.variable_toBoundaryIndex_level_eq_cutoff k

theorem sm6a_regular_noFreeEnumeration
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    L.regularSource.noFreeEnumerationStatus =
      SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a :=
  L.regularNoFreeEnumeration

theorem sm6a_variable_noFreeEnumeration
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    L.variableSource.noFreeEnumerationStatus =
      SM6aNoFreeEnumerationStatus.noFreeEnumerationInSM6a :=
  L.variableNoFreeEnumeration

theorem sm6a_regular_nextConsumerStatus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    L.regularSource.nextConsumerStatus =
      SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8 :=
  L.regularNextConsumerStatus

theorem sm6a_variable_nextConsumerStatus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6aGeneratedLevelHistoryBoundaryPortSourceLedger b β p regularWeight variableWeight) :
    L.variableSource.nextConsumerStatus =
      SM6aNextConsumerStatus.sm7BridgeRecheckRequiredBeforeSM8 :=
  L.variableNextConsumerStatus

end Smoke

end CNNA.PillarA.Arithmetic
