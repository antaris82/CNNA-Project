import CNNA.PillarA.Foundation.ExecComplexBridge
import CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM5qBoundaryOperatorProvenanceStatus where
  | realBoundaryOperatorIsSM5SM4Schur
  deriving DecidableEq, Repr

inductive SM5qExecBoundaryOperatorConstructionStatus where
  | blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  deriving DecidableEq, Repr

inductive SM5qNextPhaseStatus where
  | sm4qGeneratedMultiSchurExecBoundaryOperator
  deriving DecidableEq, Repr

inductive SM5qNoForbiddenShortcutStatus where
  | noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  deriving DecidableEq, Repr

structure GeneratedArithmeticSourceExecBoundaryOperatorWitnessSM5q
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
  sourceSM5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM5 : boundaryOperatorReal = sourceSM5.boundaryOperator
  execBoundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  exec_entry_bridge : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      (sourceSM5.boundaryOperator i j : ℂ)
  entry_eq_SM4 : ∀ i j,
    boundaryOperatorReal i j = sourceSM5.sourceMultiSchur.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  provenanceStatus : SM5qBoundaryOperatorProvenanceStatus
  provenanceStatus_eq :
    provenanceStatus =
      SM5qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM5SM4Schur

structure GeneratedArithmeticSourceExecBoundaryOperatorSM5q
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
  sourceSM5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM5 : boundaryOperatorReal = sourceSM5.boundaryOperator
  entry_eq_SM4 : ∀ i j,
    boundaryOperatorReal i j = sourceSM5.sourceMultiSchur.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  apply_eq_SM4 : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM5.«apply» φ = sourceSM5.sourceMultiSchur.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM5.«apply» φ = boundaryOperatorReal.mulVec φ
  provenanceStatus : SM5qBoundaryOperatorProvenanceStatus
  provenanceStatus_eq :
    provenanceStatus =
      SM5qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM5SM4Schur
  execBoundaryOperatorConstructionStatus : SM5qExecBoundaryOperatorConstructionStatus
  execBoundaryOperatorConstructionStatus_eq :
    execBoundaryOperatorConstructionStatus =
      SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  nextPhaseStatus : SM5qNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM5qNextPhaseStatus.sm4qGeneratedMultiSchurExecBoundaryOperator
  noForbiddenShortcutStatus : SM5qNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM5qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

namespace GeneratedArithmeticSourceExecBoundaryOperatorSM5q

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
    (S5 : GeneratedArithmeticSourceSM5 Cell p A P wp W E K T M S H G) :
    GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G where
  sourceSM5 := S5
  boundaryOperatorReal := S5.boundaryOperator
  boundaryOperatorReal_eq_SM5 := by
    rfl
  entry_eq_SM4 := by
    intro i j
    exact congrArg (fun M => M i j) S5.boundaryOperator_eq_SM4
  entry_eq_schur := by
    intro i j
    exact congrArg (fun M => M i j) S5.boundaryOperator_eq_schur
  apply_eq_SM4 := by
    intro φ
    exact S5.apply_eq_SM4 φ
  apply_eq_mulVec := by
    intro φ
    exact S5.apply_eq_mulVec φ
  provenanceStatus :=
    SM5qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM5SM4Schur
  provenanceStatus_eq := by
    rfl
  execBoundaryOperatorConstructionStatus :=
    SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  execBoundaryOperatorConstructionStatus_eq := by
    rfl
  nextPhaseStatus := SM5qNextPhaseStatus.sm4qGeneratedMultiSchurExecBoundaryOperator
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM5qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem boundaryOperatorReal_from_SM5
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G) :
    X.boundaryOperatorReal = X.sourceSM5.boundaryOperator :=
  X.boundaryOperatorReal_eq_SM5

theorem entryReal_from_SM4
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM5.sourceMultiSchur.boundaryOperator i j :=
  X.entry_eq_SM4 i j

theorem entryReal_from_schur
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          X.sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j :=
  X.entry_eq_schur i j

theorem apply_from_SM4
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM5.«apply» φ = X.sourceSM5.sourceMultiSchur.«apply» φ :=
  X.apply_eq_SM4 φ

theorem apply_from_boundaryOperatorReal_mulVec
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM5.«apply» φ = X.boundaryOperatorReal.mulVec φ :=
  X.apply_eq_mulVec φ

theorem provenance_is_SM5_SM4_schur
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G) :
    X.provenanceStatus =
      SM5qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM5SM4Schur :=
  X.provenanceStatus_eq

theorem execBoundaryOperator_blocked_missing_SM4q
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G) :
    X.execBoundaryOperatorConstructionStatus =
      SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q :=
  X.execBoundaryOperatorConstructionStatus_eq

theorem nextPhase_is_SM4q
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G) :
    X.nextPhaseStatus = SM5qNextPhaseStatus.sm4qGeneratedMultiSchurExecBoundaryOperator :=
  X.nextPhaseStatus_eq

theorem noForbiddenShortcuts_for_SM5q
    (X : GeneratedArithmeticSourceExecBoundaryOperatorSM5q Cell p A P wp W E K T M S H G) :
    X.noForbiddenShortcutStatus =
      SM5qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  X.noForbiddenShortcutStatus_eq

end GeneratedArithmeticSourceExecBoundaryOperatorSM5q

def regularGeneratedArithmeticSourceExecBoundaryOperatorSM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    GeneratedArithmeticSourceExecBoundaryOperatorSM5q
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
  GeneratedArithmeticSourceExecBoundaryOperatorSM5q.fromSM5 L.regularSource

def variableGeneratedArithmeticSourceExecBoundaryOperatorSM5q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    GeneratedArithmeticSourceExecBoundaryOperatorSM5q
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
  GeneratedArithmeticSourceExecBoundaryOperatorSM5q.fromSM5 L.variableSource

structure SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM5Ledger : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedArithmeticSourceExecBoundaryOperatorSM5q
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
  variableSource :
    GeneratedArithmeticSourceExecBoundaryOperatorSM5q
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
  regularSource_eq_from_SM5 :
    regularSource = regularGeneratedArithmeticSourceExecBoundaryOperatorSM5q sourceSM5Ledger
  variableSource_eq_from_SM5 :
    variableSource = variableGeneratedArithmeticSourceExecBoundaryOperatorSM5q sourceSM5Ledger
  regular_entry_eq_SM4 : ∀ i j,
    regularSource.boundaryOperatorReal i j =
      regularSource.sourceSM5.sourceMultiSchur.boundaryOperator i j
  variable_entry_eq_SM4 : ∀ i j,
    variableSource.boundaryOperatorReal i j =
      variableSource.sourceSM5.sourceMultiSchur.boundaryOperator i j
  regular_entry_eq_schur : ∀ i j,
    regularSource.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR
        (regularGeneratedWeightPolicyEntrySource b p regularWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (regularGeneratedWeightPolicyEntrySource b p regularWeight) *
          regularSource.sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (regularGeneratedWeightPolicyEntrySource b p regularWeight)) i j
  variable_entry_eq_schur : ∀ i j,
    variableSource.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR
        (variableGeneratedWeightPolicyEntrySource β p variableWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (variableGeneratedWeightPolicyEntrySource β p variableWeight) *
          variableSource.sourceSM5.sourceMultiSchur.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (variableGeneratedWeightPolicyEntrySource β p variableWeight)) i j
  regularConstructionStatus : SM5qExecBoundaryOperatorConstructionStatus
  regularConstructionStatus_eq :
    regularConstructionStatus =
      SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  variableConstructionStatus : SM5qExecBoundaryOperatorConstructionStatus
  variableConstructionStatus_eq :
    variableConstructionStatus =
      SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  nextPhaseStatus : SM5qNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM5qNextPhaseStatus.sm4qGeneratedMultiSchurExecBoundaryOperator
  noForbiddenShortcutStatus : SM5qNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM5qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

def sm5qGeneratedArithmeticSourceExecBoundaryOperatorLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5GeneratedArithmeticSourceLedger b β p regularWeight variableWeight) :
    SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger b β p regularWeight variableWeight where
  sourceSM5Ledger := L
  regularSource := regularGeneratedArithmeticSourceExecBoundaryOperatorSM5q L
  variableSource := variableGeneratedArithmeticSourceExecBoundaryOperatorSM5q L
  regularSource_eq_from_SM5 := by
    rfl
  variableSource_eq_from_SM5 := by
    rfl
  regular_entry_eq_SM4 := by
    intro i j
    exact (regularGeneratedArithmeticSourceExecBoundaryOperatorSM5q L).entry_eq_SM4 i j
  variable_entry_eq_SM4 := by
    intro i j
    exact (variableGeneratedArithmeticSourceExecBoundaryOperatorSM5q L).entry_eq_SM4 i j
  regular_entry_eq_schur := by
    intro i j
    exact (regularGeneratedArithmeticSourceExecBoundaryOperatorSM5q L).entry_eq_schur i j
  variable_entry_eq_schur := by
    intro i j
    exact (variableGeneratedArithmeticSourceExecBoundaryOperatorSM5q L).entry_eq_schur i j
  regularConstructionStatus :=
    SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  regularConstructionStatus_eq := by
    rfl
  variableConstructionStatus :=
    SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q
  variableConstructionStatus_eq := by
    rfl
  nextPhaseStatus := SM5qNextPhaseStatus.sm4qGeneratedMultiSchurExecBoundaryOperator
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM5qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem sm5q_regularConstruction_blocked_missingSM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.regularConstructionStatus =
      SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q :=
  L.regularConstructionStatus_eq

theorem sm5q_variableConstruction_blocked_missingSM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.variableConstructionStatus =
      SM5qExecBoundaryOperatorConstructionStatus.blockedMissingGeneratedMultiSchurExecBoundaryOperatorSM4q :=
  L.variableConstructionStatus_eq

theorem sm5q_nextPhase_is_SM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM5qNextPhaseStatus.sm4qGeneratedMultiSchurExecBoundaryOperator :=
  L.nextPhaseStatus_eq

theorem sm5q_noForbiddenShortcuts
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM5qGeneratedArithmeticSourceExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.noForbiddenShortcutStatus =
      SM5qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  L.noForbiddenShortcutStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
