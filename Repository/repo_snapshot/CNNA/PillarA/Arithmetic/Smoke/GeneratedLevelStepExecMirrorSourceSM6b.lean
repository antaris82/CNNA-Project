import CNNA.PillarA.Foundation.ExecComplexBridge
import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM6bBoundaryOperatorProvenanceStatus where
  | realBoundaryOperatorIsSM6SM5SM4Schur
  deriving DecidableEq, Repr

inductive SM6bExecMirrorConstructionStatus where
  | blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  deriving DecidableEq, Repr

inductive SM6bNextPhaseStatus where
  | sm5qGeneratedArithmeticSourceExecBoundaryOperator
  deriving DecidableEq, Repr

inductive SM6bNoForbiddenShortcutStatus where
  | noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  deriving DecidableEq, Repr

structure GeneratedLevelStepExecMirrorWitnessSM6b
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
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM6 : boundaryOperatorReal = sourceSM6Witness.boundaryOperator
  execBoundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  exec_entry_bridge : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      (sourceSM6Witness.boundaryOperator i j : ℂ)
  entry_eq_SM5 : ∀ i j,
    boundaryOperatorReal i j = sourceSM6Witness.source.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  provenanceStatus : SM6bBoundaryOperatorProvenanceStatus
  provenanceStatus_eq :
    provenanceStatus =
      SM6bBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM6SM5SM4Schur

structure GeneratedLevelStepExecMirrorSourceSM6b
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
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM6 : boundaryOperatorReal = sourceSM6Witness.boundaryOperator
  entry_eq_SM5 : ∀ i j,
    boundaryOperatorReal i j = sourceSM6Witness.source.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  apply_eq_SM5 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM6Witness.«apply» φ = sourceSM6Witness.source.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM6Witness.«apply» φ = boundaryOperatorReal.mulVec φ
  provenanceStatus : SM6bBoundaryOperatorProvenanceStatus
  provenanceStatus_eq :
    provenanceStatus =
      SM6bBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM6SM5SM4Schur
  execMirrorConstructionStatus : SM6bExecMirrorConstructionStatus
  execMirrorConstructionStatus_eq :
    execMirrorConstructionStatus =
      SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  nextPhaseStatus : SM6bNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM6bNextPhaseStatus.sm5qGeneratedArithmeticSourceExecBoundaryOperator
  noForbiddenShortcutStatus : SM6bNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM6bNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

namespace GeneratedLevelStepExecMirrorSourceSM6b

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

def fromSM6
    (W6 : GeneratedLevelStepWitnessSM6 Cell p A P wp W E K T M S H G) :
    GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G where
  sourceSM6Witness := W6
  boundaryOperatorReal := W6.boundaryOperator
  boundaryOperatorReal_eq_SM6 := by
    rfl
  entry_eq_SM5 := by
    intro i j
    exact congrArg (fun M => M i j) W6.boundaryOperator_eq_SM5
  entry_eq_schur := by
    intro i j
    exact congrArg (fun M => M i j) W6.boundaryOperator_eq_schur
  apply_eq_SM5 := by
    intro φ
    exact W6.apply_eq_SM5 φ
  apply_eq_mulVec := by
    intro φ
    exact W6.apply_eq_mulVec φ
  provenanceStatus :=
    SM6bBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM6SM5SM4Schur
  provenanceStatus_eq := by
    rfl
  execMirrorConstructionStatus :=
    SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  execMirrorConstructionStatus_eq := by
    rfl
  nextPhaseStatus := SM6bNextPhaseStatus.sm5qGeneratedArithmeticSourceExecBoundaryOperator
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM6bNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem boundaryOperatorReal_from_SM6
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G) :
    X.boundaryOperatorReal = X.sourceSM6Witness.boundaryOperator :=
  X.boundaryOperatorReal_eq_SM6

theorem entryReal_from_SM5
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM6Witness.source.boundaryOperator i j :=
  X.entry_eq_SM5 i j

theorem entryReal_from_schur
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          X.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j :=
  X.entry_eq_schur i j

theorem apply_from_SM5
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM6Witness.«apply» φ = X.sourceSM6Witness.source.«apply» φ :=
  X.apply_eq_SM5 φ

theorem apply_from_boundaryOperatorReal_mulVec
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM6Witness.«apply» φ = X.boundaryOperatorReal.mulVec φ :=
  X.apply_eq_mulVec φ

theorem provenance_is_SM6_SM5_SM4_schur
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G) :
    X.provenanceStatus =
      SM6bBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM6SM5SM4Schur :=
  X.provenanceStatus_eq

theorem execMirror_blocked_missing_SM5q
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G) :
    X.execMirrorConstructionStatus =
      SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator :=
  X.execMirrorConstructionStatus_eq

theorem nextPhase_is_SM5q
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G) :
    X.nextPhaseStatus = SM6bNextPhaseStatus.sm5qGeneratedArithmeticSourceExecBoundaryOperator :=
  X.nextPhaseStatus_eq

theorem noForbiddenShortcuts_for_SM6b
    (X : GeneratedLevelStepExecMirrorSourceSM6b Cell p A P wp W E K T M S H G) :
    X.noForbiddenShortcutStatus =
      SM6bNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  X.noForbiddenShortcutStatus_eq

end GeneratedLevelStepExecMirrorSourceSM6b

def regularGeneratedLevelStepExecMirrorSourceSM6b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    GeneratedLevelStepExecMirrorSourceSM6b
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
  GeneratedLevelStepExecMirrorSourceSM6b.fromSM6 L.regularWitness

def variableGeneratedLevelStepExecMirrorSourceSM6b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    GeneratedLevelStepExecMirrorSourceSM6b
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
  GeneratedLevelStepExecMirrorSourceSM6b.fromSM6 L.variableWitness

structure SM6bGeneratedLevelStepExecMirrorSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM6Ledger : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedLevelStepExecMirrorSourceSM6b
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
    GeneratedLevelStepExecMirrorSourceSM6b
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
  regularSource_eq_from_SM6 : regularSource = regularGeneratedLevelStepExecMirrorSourceSM6b sourceSM6Ledger
  variableSource_eq_from_SM6 : variableSource = variableGeneratedLevelStepExecMirrorSourceSM6b sourceSM6Ledger
  regular_entry_eq_SM5 : ∀ i j,
    regularSource.boundaryOperatorReal i j =
      regularSource.sourceSM6Witness.source.boundaryOperator i j
  variable_entry_eq_SM5 : ∀ i j,
    variableSource.boundaryOperatorReal i j =
      variableSource.sourceSM6Witness.source.boundaryOperator i j
  regular_entry_eq_schur : ∀ i j,
    regularSource.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR
        (regularGeneratedWeightPolicyEntrySource b p regularWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (regularGeneratedWeightPolicyEntrySource b p regularWeight) *
          regularSource.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (regularGeneratedWeightPolicyEntrySource b p regularWeight)) i j
  variable_entry_eq_schur : ∀ i j,
    variableSource.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR
        (variableGeneratedWeightPolicyEntrySource β p variableWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (variableGeneratedWeightPolicyEntrySource β p variableWeight) *
          variableSource.sourceSM6Witness.source.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (variableGeneratedWeightPolicyEntrySource β p variableWeight)) i j
  regularConstructionStatus : SM6bExecMirrorConstructionStatus
  regularConstructionStatus_eq :
    regularConstructionStatus =
      SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  variableConstructionStatus : SM6bExecMirrorConstructionStatus
  variableConstructionStatus_eq :
    variableConstructionStatus =
      SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  nextPhaseStatus : SM6bNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM6bNextPhaseStatus.sm5qGeneratedArithmeticSourceExecBoundaryOperator
  noForbiddenShortcutStatus : SM6bNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM6bNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

def sm6bGeneratedLevelStepExecMirrorSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6GeneratedLevelStepWitnessLedger b β p regularWeight variableWeight) :
    SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight where
  sourceSM6Ledger := L
  regularSource := regularGeneratedLevelStepExecMirrorSourceSM6b L
  variableSource := variableGeneratedLevelStepExecMirrorSourceSM6b L
  regularSource_eq_from_SM6 := by
    rfl
  variableSource_eq_from_SM6 := by
    rfl
  regular_entry_eq_SM5 := by
    intro i j
    exact (regularGeneratedLevelStepExecMirrorSourceSM6b L).entry_eq_SM5 i j
  variable_entry_eq_SM5 := by
    intro i j
    exact (variableGeneratedLevelStepExecMirrorSourceSM6b L).entry_eq_SM5 i j
  regular_entry_eq_schur := by
    intro i j
    exact (regularGeneratedLevelStepExecMirrorSourceSM6b L).entry_eq_schur i j
  variable_entry_eq_schur := by
    intro i j
    exact (variableGeneratedLevelStepExecMirrorSourceSM6b L).entry_eq_schur i j
  regularConstructionStatus :=
    SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  regularConstructionStatus_eq := by
    rfl
  variableConstructionStatus :=
    SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator
  variableConstructionStatus_eq := by
    rfl
  nextPhaseStatus := SM6bNextPhaseStatus.sm5qGeneratedArithmeticSourceExecBoundaryOperator
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM6bNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

def sm6bGeneratedLevelStepExecMirrorSourceLedger_from_SM5
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level) :
    SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight :=
  sm6bGeneratedLevelStepExecMirrorSourceLedger
    (sm6GeneratedLevelStepWitnessLedger L level levelIndex)

theorem sm6b_regularConstruction_blocked_missingSM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.regularConstructionStatus =
      SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator :=
  L.regularConstructionStatus_eq

theorem sm6b_variableConstruction_blocked_missingSM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.variableConstructionStatus =
      SM6bExecMirrorConstructionStatus.blockedMissingGeneratedArithmeticSourceExecBoundaryOperator :=
  L.variableConstructionStatus_eq

theorem sm6b_nextPhase_is_SM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM6bNextPhaseStatus.sm5qGeneratedArithmeticSourceExecBoundaryOperator :=
  L.nextPhaseStatus_eq

theorem sm6b_noForbiddenShortcuts
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM6bGeneratedLevelStepExecMirrorSourceLedger b β p regularWeight variableWeight) :
    L.noForbiddenShortcutStatus =
      SM6bNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  L.noForbiddenShortcutStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
