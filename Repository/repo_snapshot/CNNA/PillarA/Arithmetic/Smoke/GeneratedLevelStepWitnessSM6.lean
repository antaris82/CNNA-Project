import CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

abbrev GeneratedLevelHistoryIndexSM6 (L : Nat) :=
  Fin (L + 1)

inductive SM6NoCutSpecCarrierClaimStatus where
  | noCutSpecCarrierClaimInSM6
  deriving DecidableEq, Repr

inductive SM6NoSchurIndexBridgeStatus where
  | noSchurIndexBridgeInSM6
  deriving DecidableEq, Repr

inductive SM6NoLevelHistoryMatrixStatus where
  | noLevelHistoryMatrixInSM6
  deriving DecidableEq, Repr

inductive SM6NoCharpolyDiscriminantStatus where
  | noCharpolyFactorDiscriminantDataInSM6
  deriving DecidableEq, Repr

structure GeneratedLevelStepWitnessSM6
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
  sourceSM5Ledger : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G
  level : Nat
  levelIndex : GeneratedLevelHistoryIndexSM6 level
  source : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G
  source_eq_SM5 : source = sourceSM5Ledger
  boundaryCarrier : Type u
  boundaryCarrier_eq_generated : boundaryCarrier = GeneratedBoundaryIndex A
  boundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperator_eq_SM5 : boundaryOperator = source.boundaryOperator
  boundaryOperator_eq_schur :
    boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  «apply» : (GeneratedBoundaryIndex A → ℝ) → GeneratedBoundaryIndex A → ℝ
  apply_eq_SM5 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = source.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = boundaryOperator.mulVec φ
  noCutSpecCarrierClaimStatus : SM6NoCutSpecCarrierClaimStatus
  noCutSpecCarrierClaimStatus_eq :
    noCutSpecCarrierClaimStatus =
      SM6NoCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM6
  noSchurIndexBridgeStatus : SM6NoSchurIndexBridgeStatus
  noSchurIndexBridgeStatus_eq :
    noSchurIndexBridgeStatus = SM6NoSchurIndexBridgeStatus.noSchurIndexBridgeInSM6
  noLevelHistoryMatrixStatus : SM6NoLevelHistoryMatrixStatus
  noLevelHistoryMatrixStatus_eq :
    noLevelHistoryMatrixStatus = SM6NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM6
  noCharpolyDiscriminantStatus : SM6NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM6NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6

namespace GeneratedLevelStepWitnessSM6

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

def fromSM5
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G where
  sourceSM5Ledger := S5
  level := level
  levelIndex := levelIndex
  source := S5
  source_eq_SM5 := by
    rfl
  boundaryCarrier := GeneratedBoundaryIndex A
  boundaryCarrier_eq_generated := by
    rfl
  boundaryOperator := S5.boundaryOperator
  boundaryOperator_eq_SM5 := by
    rfl
  boundaryOperator_eq_schur := by
    exact S5.boundaryOperator_eq_schur
  «apply» := S5.«apply»
  apply_eq_SM5 := by
    intro φ
    rfl
  apply_eq_mulVec := by
    intro φ
    exact S5.apply_eq_mulVec φ
  noCutSpecCarrierClaimStatus := SM6NoCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM6
  noCutSpecCarrierClaimStatus_eq := by
    rfl
  noSchurIndexBridgeStatus := SM6NoSchurIndexBridgeStatus.noSchurIndexBridgeInSM6
  noSchurIndexBridgeStatus_eq := by
    rfl
  noLevelHistoryMatrixStatus := SM6NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM6
  noLevelHistoryMatrixStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM6NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6
  noCharpolyDiscriminantStatus_eq := by
    rfl

theorem source_from_SM5
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.source = W6.sourceSM5Ledger :=
  W6.source_eq_SM5

theorem boundaryCarrier_is_generated
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.boundaryCarrier = GeneratedBoundaryIndex A :=
  W6.boundaryCarrier_eq_generated

theorem boundaryOperator_from_SM5
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.boundaryOperator = W6.source.boundaryOperator :=
  W6.boundaryOperator_eq_SM5

theorem boundaryOperator_from_schur
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          W6.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  W6.boundaryOperator_eq_schur

theorem apply_from_SM5
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    W6.«apply» φ = W6.source.«apply» φ :=
  W6.apply_eq_SM5 φ

theorem apply_from_mulVec
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    W6.«apply» φ = W6.boundaryOperator.mulVec φ :=
  W6.apply_eq_mulVec φ

theorem noCutSpecCarrierClaim_for_SM6
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.noCutSpecCarrierClaimStatus =
      SM6NoCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM6 :=
  W6.noCutSpecCarrierClaimStatus_eq

theorem noSchurIndexBridge_for_SM6
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.noSchurIndexBridgeStatus = SM6NoSchurIndexBridgeStatus.noSchurIndexBridgeInSM6 :=
  W6.noSchurIndexBridgeStatus_eq

theorem noLevelHistoryMatrix_for_SM6
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.noLevelHistoryMatrixStatus =
      SM6NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM6 :=
  W6.noLevelHistoryMatrixStatus_eq

theorem noCharpolyDiscriminant_for_SM6
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    W6.noCharpolyDiscriminantStatus =
      SM6NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6 :=
  W6.noCharpolyDiscriminantStatus_eq

end GeneratedLevelStepWitnessSM6

def regularGeneratedLevelStepWitness_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
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
      L.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelStepWitnessSM6.fromSM5 L.regularSource level levelIndex

def variableGeneratedLevelStepWitness_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
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
      L.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelStepWitnessSM6.fromSM5 L.variableSource level levelIndex

structure SM6GeneratedLevelStepWitnessLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM5Ledger : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight
  level : Nat
  levelIndex : GeneratedLevelHistoryIndexSM6 level
  regularWitness :
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
      sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableWitness :
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
      sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regular_source_eq_SM5 : regularWitness.source = sourceSM5Ledger.regularSource
  variable_source_eq_SM5 : variableWitness.source = sourceSM5Ledger.variableSource
  regular_source_eq_SM4 :
    regularWitness.source.sourceMultiSchur = sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variable_source_eq_SM4 :
    variableWitness.source.sourceMultiSchur = sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regular_boundaryCarrier_eq_generated :
    regularWitness.boundaryCarrier = GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p)
  variable_boundaryCarrier_eq_generated :
    variableWitness.boundaryCarrier = GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p)
  regular_boundaryOperator_eq_SM5 :
    regularWitness.boundaryOperator = sourceSM5Ledger.regularSource.boundaryOperator
  variable_boundaryOperator_eq_SM5 :
    variableWitness.boundaryOperator = sourceSM5Ledger.variableSource.boundaryOperator
  regular_boundaryOperator_eq_schur :
    regularWitness.boundaryOperator =
      generatedBoundaryBlockSM3fR
        (regularGeneratedWeightPolicyEntrySource b p regularWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (regularGeneratedWeightPolicyEntrySource b p regularWeight) *
          regularWitness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variable_boundaryOperator_eq_schur :
    variableWitness.boundaryOperator =
      generatedBoundaryBlockSM3fR
        (variableGeneratedWeightPolicyEntrySource β p variableWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (variableGeneratedWeightPolicyEntrySource β p variableWeight) *
          variableWitness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  regular_apply_eq_SM5 : ∀ φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ,
    regularWitness.«apply» φ = sourceSM5Ledger.regularSource.«apply» φ
  variable_apply_eq_SM5 : ∀ φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ,
    variableWitness.«apply» φ = sourceSM5Ledger.variableSource.«apply» φ
  regular_apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ,
    regularWitness.«apply» φ = regularWitness.boundaryOperator.mulVec φ
  variable_apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ,
    variableWitness.«apply» φ = variableWitness.boundaryOperator.mulVec φ
  regular_noCutSpecCarrierClaimStatus :
    regularWitness.noCutSpecCarrierClaimStatus =
      SM6NoCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM6
  variable_noCutSpecCarrierClaimStatus :
    variableWitness.noCutSpecCarrierClaimStatus =
      SM6NoCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM6
  regular_noSchurIndexBridgeStatus :
    regularWitness.noSchurIndexBridgeStatus = SM6NoSchurIndexBridgeStatus.noSchurIndexBridgeInSM6
  variable_noSchurIndexBridgeStatus :
    variableWitness.noSchurIndexBridgeStatus = SM6NoSchurIndexBridgeStatus.noSchurIndexBridgeInSM6
  regular_noLevelHistoryMatrixStatus :
    regularWitness.noLevelHistoryMatrixStatus =
      SM6NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM6
  variable_noLevelHistoryMatrixStatus :
    variableWitness.noLevelHistoryMatrixStatus =
      SM6NoLevelHistoryMatrixStatus.noLevelHistoryMatrixInSM6
  regular_noCharpolyDiscriminantStatus :
    regularWitness.noCharpolyDiscriminantStatus =
      SM6NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6
  variable_noCharpolyDiscriminantStatus :
    variableWitness.noCharpolyDiscriminantStatus =
      SM6NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM6

def sm6GeneratedLevelStepWitnessLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight where
  sourceSM5Ledger := L
  level := level
  levelIndex := levelIndex
  regularWitness := regularGeneratedLevelStepWitness_from_SM5 L level levelIndex
  variableWitness := variableGeneratedLevelStepWitness_from_SM5 L level levelIndex
  regular_source_eq_SM5 := by
    rfl
  variable_source_eq_SM5 := by
    rfl
  regular_source_eq_SM4 := by
    exact L.regularSource_eq_SM4
  variable_source_eq_SM4 := by
    exact L.variableSource_eq_SM4
  regular_boundaryCarrier_eq_generated := by
    rfl
  variable_boundaryCarrier_eq_generated := by
    rfl
  regular_boundaryOperator_eq_SM5 := by
    rfl
  variable_boundaryOperator_eq_SM5 := by
    rfl
  regular_boundaryOperator_eq_schur := by
    exact L.regularSource.boundaryOperator_eq_schur
  variable_boundaryOperator_eq_schur := by
    exact L.variableSource.boundaryOperator_eq_schur
  regular_apply_eq_SM5 := by
    intro φ
    rfl
  variable_apply_eq_SM5 := by
    intro φ
    rfl
  regular_apply_eq_mulVec := by
    intro φ
    exact L.regularSource.apply_eq_mulVec φ
  variable_apply_eq_mulVec := by
    intro φ
    exact L.variableSource.apply_eq_mulVec φ
  regular_noCutSpecCarrierClaimStatus := by
    rfl
  variable_noCutSpecCarrierClaimStatus := by
    rfl
  regular_noSchurIndexBridgeStatus := by
    rfl
  variable_noSchurIndexBridgeStatus := by
    rfl
  regular_noLevelHistoryMatrixStatus := by
    rfl
  variable_noLevelHistoryMatrixStatus := by
    rfl
  regular_noCharpolyDiscriminantStatus := by
    rfl
  variable_noCharpolyDiscriminantStatus := by
    rfl

def sm6GeneratedLevelStepWitnessLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight :=
  sm6GeneratedLevelStepWitnessLedger
    (sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger L)
    level levelIndex

theorem sm6GeneratedLevelStepWitnessLedger_regular_source_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    L.regularWitness.source = L.sourceSM5Ledger.regularSource :=
  L.regular_source_eq_SM5

theorem sm6GeneratedLevelStepWitnessLedger_variable_source_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    L.variableWitness.source = L.sourceSM5Ledger.variableSource :=
  L.variable_source_eq_SM5

theorem sm6GeneratedLevelStepWitnessLedger_regular_boundaryOperator_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    L.regularWitness.boundaryOperator = L.sourceSM5Ledger.regularSource.boundaryOperator :=
  L.regular_boundaryOperator_eq_SM5

theorem sm6GeneratedLevelStepWitnessLedger_variable_boundaryOperator_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    L.variableWitness.boundaryOperator = L.sourceSM5Ledger.variableSource.boundaryOperator :=
  L.variable_boundaryOperator_eq_SM5

theorem sm6GeneratedLevelStepWitnessLedger_regular_apply_eq_mulVec
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight)
    (φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ) :
    L.regularWitness.«apply» φ = L.regularWitness.boundaryOperator.mulVec φ :=
  L.regular_apply_eq_mulVec φ

theorem sm6GeneratedLevelStepWitnessLedger_variable_apply_eq_mulVec
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight)
    (φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ) :
    L.variableWitness.«apply» φ = L.variableWitness.boundaryOperator.mulVec φ :=
  L.variable_apply_eq_mulVec φ

end Smoke

end CNNA.PillarA.Arithmetic
