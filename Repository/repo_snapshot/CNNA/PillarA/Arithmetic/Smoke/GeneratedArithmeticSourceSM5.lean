import CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive GeneratedArithmeticSourceKindSM5 where
  | regularGenerated
  | variableGenerated
  deriving DecidableEq, Repr

inductive SM5SourceSM4Status where
  | sourceIsSM4GeneratedMultiSchurLedger
  deriving DecidableEq, Repr

inductive SM5NoNewToCGeneratorStatus where
  | noNewToCGeneratorInSM5
  deriving DecidableEq, Repr

inductive SM5NoPublicMultiSchurStrongForcedStatus where
  | noPublicMultiSchurStrongForcedInSM5
  deriving DecidableEq, Repr

inductive SM5NoLevelHistoryStatus where
  | noLevelHistoryDataInSM5
  deriving DecidableEq, Repr

inductive SM5NoCharpolyDiscriminantStatus where
  | noCharpolyFactorDiscriminantDataInSM5
  deriving DecidableEq, Repr

structure GeneratedArithmeticSourceSM5
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
  kind : GeneratedArithmeticSourceKindSM5
  sourceSM4Status : SM5SourceSM4Status
  sourceSM4Status_eq :
    sourceSM4Status = SM5SourceSM4Status.sourceIsSM4GeneratedMultiSchurLedger
  sourceMultiSchur : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H
  source_eq_SM4 : sourceMultiSchur = G
  boundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperator_eq_SM4 : boundaryOperator = sourceMultiSchur.boundaryOperator
  boundaryOperator_eq_schur :
    boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  «apply» : (GeneratedBoundaryIndex A → ℝ) → GeneratedBoundaryIndex A → ℝ
  apply_eq_SM4 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = sourceMultiSchur.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = boundaryOperator.mulVec φ
  noNewToCGeneratorStatus : SM5NoNewToCGeneratorStatus
  noNewToCGeneratorStatus_eq :
    noNewToCGeneratorStatus = SM5NoNewToCGeneratorStatus.noNewToCGeneratorInSM5
  noPublicMultiSchurStrongForcedStatus : SM5NoPublicMultiSchurStrongForcedStatus
  noPublicMultiSchurStrongForcedStatus_eq :
    noPublicMultiSchurStrongForcedStatus =
      SM5NoPublicMultiSchurStrongForcedStatus.noPublicMultiSchurStrongForcedInSM5
  noLevelHistoryStatus : SM5NoLevelHistoryStatus
  noLevelHistoryStatus_eq :
    noLevelHistoryStatus = SM5NoLevelHistoryStatus.noLevelHistoryDataInSM5
  noCharpolyDiscriminantStatus : SM5NoCharpolyDiscriminantStatus
  noCharpolyDiscriminantStatus_eq :
    noCharpolyDiscriminantStatus =
      SM5NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM5

namespace GeneratedArithmeticSourceSM5

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

def fromSM4
    (kind : GeneratedArithmeticSourceKindSM5)
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G where
  kind := kind
  sourceSM4Status := SM5SourceSM4Status.sourceIsSM4GeneratedMultiSchurLedger
  sourceSM4Status_eq := by
    rfl
  sourceMultiSchur := G
  source_eq_SM4 := by
    rfl
  boundaryOperator := G.boundaryOperator
  boundaryOperator_eq_SM4 := by
    rfl
  boundaryOperator_eq_schur := by
    exact G.boundaryOperator_eq_schur
  «apply» := G.«apply»
  apply_eq_SM4 := by
    intro φ
    rfl
  apply_eq_mulVec := by
    intro φ
    exact G.apply_eq_mulVec φ
  noNewToCGeneratorStatus := SM5NoNewToCGeneratorStatus.noNewToCGeneratorInSM5
  noNewToCGeneratorStatus_eq := by
    rfl
  noPublicMultiSchurStrongForcedStatus :=
    SM5NoPublicMultiSchurStrongForcedStatus.noPublicMultiSchurStrongForcedInSM5
  noPublicMultiSchurStrongForcedStatus_eq := by
    rfl
  noLevelHistoryStatus := SM5NoLevelHistoryStatus.noLevelHistoryDataInSM5
  noLevelHistoryStatus_eq := by
    rfl
  noCharpolyDiscriminantStatus :=
    SM5NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM5
  noCharpolyDiscriminantStatus_eq := by
    rfl

theorem sourceMultiSchur_from_SM4
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.sourceMultiSchur = G :=
  S5.source_eq_SM4

theorem boundaryOperator_from_SM4
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.boundaryOperator = S5.sourceMultiSchur.boundaryOperator :=
  S5.boundaryOperator_eq_SM4

theorem boundaryOperator_from_schur
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          S5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  S5.boundaryOperator_eq_schur

theorem apply_from_SM4
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    S5.«apply» φ = S5.sourceMultiSchur.«apply» φ :=
  S5.apply_eq_SM4 φ

theorem apply_from_mulVec
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    S5.«apply» φ = S5.boundaryOperator.mulVec φ :=
  S5.apply_eq_mulVec φ

theorem noNewToCGenerator_for_SM5
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.noNewToCGeneratorStatus =
      SM5NoNewToCGeneratorStatus.noNewToCGeneratorInSM5 :=
  S5.noNewToCGeneratorStatus_eq

theorem noPublicMultiSchurStrongForced_for_SM5
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.noPublicMultiSchurStrongForcedStatus =
      SM5NoPublicMultiSchurStrongForcedStatus.noPublicMultiSchurStrongForcedInSM5 :=
  S5.noPublicMultiSchurStrongForcedStatus_eq

theorem noLevelHistory_for_SM5
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.noLevelHistoryStatus = SM5NoLevelHistoryStatus.noLevelHistoryDataInSM5 :=
  S5.noLevelHistoryStatus_eq

theorem noCharpolyDiscriminant_for_SM5
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    S5.noCharpolyDiscriminantStatus =
      SM5NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM5 :=
  S5.noCharpolyDiscriminantStatus_eq

end GeneratedArithmeticSourceSM5

def regularGeneratedArithmeticSource_from_SM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    GeneratedArithmeticSourceSM5
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.regularMultiSchur :=
  GeneratedArithmeticSourceSM5.fromSM4
    GeneratedArithmeticSourceKindSM5.regularGenerated L.regularMultiSchur

def variableGeneratedArithmeticSource_from_SM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    GeneratedArithmeticSourceSM5
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.variableMultiSchur :=
  GeneratedArithmeticSourceSM5.fromSM4
    GeneratedArithmeticSourceKindSM5.variableGenerated L.variableMultiSchur

structure SM5GeneratedArithmeticSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM4Ledger : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedArithmeticSourceSM5
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM4Ledger.regularMultiSchur
  variableSource :
    GeneratedArithmeticSourceSM5
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM4Ledger.variableMultiSchur
  regularSourceKind : regularSource.kind = GeneratedArithmeticSourceKindSM5.regularGenerated
  variableSourceKind : variableSource.kind = GeneratedArithmeticSourceKindSM5.variableGenerated
  regularSource_eq_SM4 : regularSource.sourceMultiSchur = sourceSM4Ledger.regularMultiSchur
  variableSource_eq_SM4 : variableSource.sourceMultiSchur = sourceSM4Ledger.variableMultiSchur
  regular_boundaryOperator_eq_SM4 :
    regularSource.boundaryOperator = sourceSM4Ledger.regularMultiSchur.boundaryOperator
  variable_boundaryOperator_eq_SM4 :
    variableSource.boundaryOperator = sourceSM4Ledger.variableMultiSchur.boundaryOperator
  regular_boundaryOperator_eq_schur :
    regularSource.boundaryOperator =
      generatedBoundaryBlockSM3fR
        (regularGeneratedWeightPolicyEntrySource b p regularWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (regularGeneratedWeightPolicyEntrySource b p regularWeight) *
          sourceSM4Ledger.regularMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variable_boundaryOperator_eq_schur :
    variableSource.boundaryOperator =
      generatedBoundaryBlockSM3fR
        (variableGeneratedWeightPolicyEntrySource β p variableWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (variableGeneratedWeightPolicyEntrySource β p variableWeight) *
          sourceSM4Ledger.variableMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  regular_apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ,
    regularSource.«apply» φ = regularSource.boundaryOperator.mulVec φ
  variable_apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ,
    variableSource.«apply» φ = variableSource.boundaryOperator.mulVec φ
  regular_noNewToCGeneratorStatus :
    regularSource.noNewToCGeneratorStatus = SM5NoNewToCGeneratorStatus.noNewToCGeneratorInSM5
  variable_noNewToCGeneratorStatus :
    variableSource.noNewToCGeneratorStatus = SM5NoNewToCGeneratorStatus.noNewToCGeneratorInSM5
  regular_noPublicMultiSchurStrongForcedStatus :
    regularSource.noPublicMultiSchurStrongForcedStatus =
      SM5NoPublicMultiSchurStrongForcedStatus.noPublicMultiSchurStrongForcedInSM5
  variable_noPublicMultiSchurStrongForcedStatus :
    variableSource.noPublicMultiSchurStrongForcedStatus =
      SM5NoPublicMultiSchurStrongForcedStatus.noPublicMultiSchurStrongForcedInSM5
  regular_noLevelHistoryStatus :
    regularSource.noLevelHistoryStatus = SM5NoLevelHistoryStatus.noLevelHistoryDataInSM5
  variable_noLevelHistoryStatus :
    variableSource.noLevelHistoryStatus = SM5NoLevelHistoryStatus.noLevelHistoryDataInSM5
  regular_noCharpolyDiscriminantStatus :
    regularSource.noCharpolyDiscriminantStatus =
      SM5NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM5
  variable_noCharpolyDiscriminantStatus :
    variableSource.noCharpolyDiscriminantStatus =
      SM5NoCharpolyDiscriminantStatus.noCharpolyFactorDiscriminantDataInSM5

def sm5GeneratedArithmeticSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight where
  sourceSM4Ledger := L
  regularSource := regularGeneratedArithmeticSource_from_SM4 L
  variableSource := variableGeneratedArithmeticSource_from_SM4 L
  regularSourceKind := by
    rfl
  variableSourceKind := by
    rfl
  regularSource_eq_SM4 := by
    rfl
  variableSource_eq_SM4 := by
    rfl
  regular_boundaryOperator_eq_SM4 := by
    rfl
  variable_boundaryOperator_eq_SM4 := by
    rfl
  regular_boundaryOperator_eq_schur := by
    exact L.regularMultiSchur.boundaryOperator_eq_schur
  variable_boundaryOperator_eq_schur := by
    exact L.variableMultiSchur.boundaryOperator_eq_schur
  regular_apply_eq_mulVec := by
    intro φ
    exact L.regularMultiSchur.apply_eq_mulVec φ
  variable_apply_eq_mulVec := by
    intro φ
    exact L.variableMultiSchur.apply_eq_mulVec φ
  regular_noNewToCGeneratorStatus := by
    rfl
  variable_noNewToCGeneratorStatus := by
    rfl
  regular_noPublicMultiSchurStrongForcedStatus := by
    rfl
  variable_noPublicMultiSchurStrongForcedStatus := by
    rfl
  regular_noLevelHistoryStatus := by
    rfl
  variable_noLevelHistoryStatus := by
    rfl
  regular_noCharpolyDiscriminantStatus := by
    rfl
  variable_noCharpolyDiscriminantStatus := by
    rfl

def sm5GeneratedArithmeticSourceLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight :=
  sm5GeneratedArithmeticSourceLedger
    (sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger L)

theorem sm5GeneratedArithmeticSourceLedger_regular_source_from_SM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    L.regularSource.sourceMultiSchur = L.sourceSM4Ledger.regularMultiSchur :=
  L.regularSource_eq_SM4

theorem sm5GeneratedArithmeticSourceLedger_variable_source_from_SM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    L.variableSource.sourceMultiSchur = L.sourceSM4Ledger.variableMultiSchur :=
  L.variableSource_eq_SM4

theorem sm5GeneratedArithmeticSourceLedger_regular_boundaryOperator_from_SM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    L.regularSource.boundaryOperator = L.sourceSM4Ledger.regularMultiSchur.boundaryOperator :=
  L.regular_boundaryOperator_eq_SM4

theorem sm5GeneratedArithmeticSourceLedger_variable_boundaryOperator_from_SM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    L.variableSource.boundaryOperator = L.sourceSM4Ledger.variableMultiSchur.boundaryOperator :=
  L.variable_boundaryOperator_eq_SM4

theorem sm5GeneratedArithmeticSourceLedger_regular_apply_eq_mulVec
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ) :
    L.regularSource.«apply» φ = L.regularSource.boundaryOperator.mulVec φ :=
  L.regular_apply_eq_mulVec φ

theorem sm5GeneratedArithmeticSourceLedger_variable_apply_eq_mulVec
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ) :
    L.variableSource.«apply» φ = L.variableSource.boundaryOperator.mulVec φ :=
  L.variable_apply_eq_mulVec φ

end Smoke

end CNNA.PillarA.Arithmetic
