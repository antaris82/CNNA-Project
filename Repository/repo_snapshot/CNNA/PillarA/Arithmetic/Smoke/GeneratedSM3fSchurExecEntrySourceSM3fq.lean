import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM3fqSchurEntrySourceStatus where
  | realSchurEntriesFromSM3fCertificate
  deriving DecidableEq, Repr

inductive SM3fqExecConstructionStatus where
  | blockedMissingOperationalExecSubsources
  deriving DecidableEq, Repr

inductive SM3fqMissingSubsourceGate where
  | missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  deriving DecidableEq, Repr

inductive SM3fqNextPhaseStatus where
  | sm3bqGeneratedDirichletExecEntrySource
  deriving DecidableEq, Repr

inductive SM3fqNoForbiddenShortcutStatus where
  | noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  deriving DecidableEq, Repr

structure GeneratedSM3fSchurExecEntrySourceSM3fq
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) where
  sourceCertificate :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H
  boundaryBlockReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryBlockReal_eq_SM3f : boundaryBlockReal = generatedBoundaryBlockSM3fR W
  boundaryInteriorBlockReal :
    Matrix (GeneratedBoundaryIndex A) (GeneratedInteriorIndex A) ℝ
  boundaryInteriorBlockReal_eq_SM3f :
    boundaryInteriorBlockReal = generatedBoundaryInteriorBlockSM3fR W
  interiorBoundaryBlockReal :
    Matrix (GeneratedInteriorIndex A) (GeneratedBoundaryIndex A) ℝ
  interiorBoundaryBlockReal_eq_SM3f :
    interiorBoundaryBlockReal = generatedInteriorBoundaryBlockSM3fR W
  inverseMatrixReal : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ
  inverseMatrixReal_eq_certificate : inverseMatrixReal = sourceCertificate.inverseMatrix
  inverseMatrixReal_eq_handoffCandidate : inverseMatrixReal = H.candidateMatrix
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_certificate : boundaryOperatorReal = sourceCertificate.boundaryOperator
  boundaryOperatorReal_eq_schur :
    boundaryOperatorReal =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * inverseMatrixReal *
          generatedInteriorBoundaryBlockSM3fR W
  sourceStatus : SM3fqSchurEntrySourceStatus
  sourceStatus_eq :
    sourceStatus = SM3fqSchurEntrySourceStatus.realSchurEntriesFromSM3fCertificate
  execConstructionStatus : SM3fqExecConstructionStatus
  execConstructionStatus_eq :
    execConstructionStatus = SM3fqExecConstructionStatus.blockedMissingOperationalExecSubsources
  missingSubsourceGate : SM3fqMissingSubsourceGate
  missingSubsourceGate_eq :
    missingSubsourceGate =
      SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  nextPhaseStatus : SM3fqNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3fqNextPhaseStatus.sm3bqGeneratedDirichletExecEntrySource
  noForbiddenShortcutStatus : SM3fqNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM3fqNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

namespace GeneratedSM3fSchurExecEntrySourceSM3fq

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

def fromCertificate
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H where
  sourceCertificate := C
  boundaryBlockReal := generatedBoundaryBlockSM3fR W
  boundaryBlockReal_eq_SM3f := by
    rfl
  boundaryInteriorBlockReal := generatedBoundaryInteriorBlockSM3fR W
  boundaryInteriorBlockReal_eq_SM3f := by
    rfl
  interiorBoundaryBlockReal := generatedInteriorBoundaryBlockSM3fR W
  interiorBoundaryBlockReal_eq_SM3f := by
    rfl
  inverseMatrixReal := C.inverseMatrix
  inverseMatrixReal_eq_certificate := by
    rfl
  inverseMatrixReal_eq_handoffCandidate := by
    exact C.inverseMatrix_eq_handoffCandidate
  boundaryOperatorReal := C.boundaryOperator
  boundaryOperatorReal_eq_certificate := by
    rfl
  boundaryOperatorReal_eq_schur := by
    exact C.boundaryOperator_eq_schur
  sourceStatus := SM3fqSchurEntrySourceStatus.realSchurEntriesFromSM3fCertificate
  sourceStatus_eq := by
    rfl
  execConstructionStatus := SM3fqExecConstructionStatus.blockedMissingOperationalExecSubsources
  execConstructionStatus_eq := by
    rfl
  missingSubsourceGate :=
    SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  missingSubsourceGate_eq := by
    rfl
  nextPhaseStatus := SM3fqNextPhaseStatus.sm3bqGeneratedDirichletExecEntrySource
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM3fqNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem boundaryBlockReal_from_SM3f
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.boundaryBlockReal = generatedBoundaryBlockSM3fR W :=
  X.boundaryBlockReal_eq_SM3f

theorem boundaryInteriorBlockReal_from_SM3f
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.boundaryInteriorBlockReal = generatedBoundaryInteriorBlockSM3fR W :=
  X.boundaryInteriorBlockReal_eq_SM3f

theorem interiorBoundaryBlockReal_from_SM3f
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.interiorBoundaryBlockReal = generatedInteriorBoundaryBlockSM3fR W :=
  X.interiorBoundaryBlockReal_eq_SM3f

theorem inverseMatrixReal_from_certificate
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.inverseMatrixReal = X.sourceCertificate.inverseMatrix :=
  X.inverseMatrixReal_eq_certificate

theorem inverseMatrixReal_from_handoffCandidate
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.inverseMatrixReal = H.candidateMatrix :=
  X.inverseMatrixReal_eq_handoffCandidate

theorem boundaryOperatorReal_from_certificate
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.boundaryOperatorReal = X.sourceCertificate.boundaryOperator :=
  X.boundaryOperatorReal_eq_certificate

theorem boundaryOperatorReal_from_schur
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.boundaryOperatorReal =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * X.inverseMatrixReal *
          generatedInteriorBoundaryBlockSM3fR W :=
  X.boundaryOperatorReal_eq_schur

theorem sourceStatus_is_SM3f_certificate
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.sourceStatus = SM3fqSchurEntrySourceStatus.realSchurEntriesFromSM3fCertificate :=
  X.sourceStatus_eq

theorem execConstruction_blocked_missing_operational_subsources
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.execConstructionStatus = SM3fqExecConstructionStatus.blockedMissingOperationalExecSubsources :=
  X.execConstructionStatus_eq

theorem missingSubsourceGate_is_SM3bq_first
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.missingSubsourceGate =
      SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries :=
  X.missingSubsourceGate_eq

theorem nextPhase_is_SM3bq
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.nextPhaseStatus = SM3fqNextPhaseStatus.sm3bqGeneratedDirichletExecEntrySource :=
  X.nextPhaseStatus_eq

theorem noForbiddenShortcuts_for_SM3fq
    (X : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    X.noForbiddenShortcutStatus =
      SM3fqNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  X.noForbiddenShortcutStatus_eq

end GeneratedSM3fSchurExecEntrySourceSM3fq

def regularGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedSM3fSchurExecEntrySourceSM3fq
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedSM3fSchurExecEntrySourceSM3fq.fromCertificate
    (regularGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR L)

def variableGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedSM3fSchurExecEntrySourceSM3fq
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedSM3fSchurExecEntrySourceSM3fq.fromCertificate
    (variableGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR L)

structure SM3fqGeneratedSM3fSchurExecEntrySourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM3fLedger : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedSM3fSchurExecEntrySourceSM3fq
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableSource :
    GeneratedSM3fSchurExecEntrySourceSM3fq
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularSource_eq_from_SM3f :
    regularSource =
      regularGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq
        sourceSM3fLedger
  variableSource_eq_from_SM3f :
    variableSource =
      variableGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq
        sourceSM3fLedger
  regularMissingSubsourceGate : SM3fqMissingSubsourceGate
  regularMissingSubsourceGate_eq :
    regularMissingSubsourceGate =
      SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  variableMissingSubsourceGate : SM3fqMissingSubsourceGate
  variableMissingSubsourceGate_eq :
    variableMissingSubsourceGate =
      SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  nextPhaseStatus : SM3fqNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3fqNextPhaseStatus.sm3bqGeneratedDirichletExecEntrySource
  noForbiddenShortcutStatus : SM3fqNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM3fqNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

def sm3fqGeneratedSM3fSchurExecEntrySourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM3fqGeneratedSM3fSchurExecEntrySourceLedger b β p regularWeight variableWeight where
  sourceSM3fLedger := L
  regularSource :=
    regularGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq L
  variableSource :=
    variableGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq L
  regularSource_eq_from_SM3f := by
    rfl
  variableSource_eq_from_SM3f := by
    rfl
  regularMissingSubsourceGate :=
    SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  regularMissingSubsourceGate_eq := by
    rfl
  variableMissingSubsourceGate :=
    SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries
  variableMissingSubsourceGate_eq := by
    rfl
  nextPhaseStatus := SM3fqNextPhaseStatus.sm3bqGeneratedDirichletExecEntrySource
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM3fqNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem sm3fq_regular_missingSubsourceGate_is_SM3bq_first
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqGeneratedSM3fSchurExecEntrySourceLedger b β p regularWeight variableWeight) :
    L.regularMissingSubsourceGate =
      SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries :=
  L.regularMissingSubsourceGate_eq

theorem sm3fq_variable_missingSubsourceGate_is_SM3bq_first
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqGeneratedSM3fSchurExecEntrySourceLedger b β p regularWeight variableWeight) :
    L.variableMissingSubsourceGate =
      SM3fqMissingSubsourceGate.missingSM3bqDirichletWeightPolicyExecEntriesBeforeInverseExecEntries :=
  L.variableMissingSubsourceGate_eq

theorem sm3fq_nextPhase_is_SM3bq
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqGeneratedSM3fSchurExecEntrySourceLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM3fqNextPhaseStatus.sm3bqGeneratedDirichletExecEntrySource :=
  L.nextPhaseStatus_eq

theorem sm3fq_noForbiddenShortcuts
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqGeneratedSM3fSchurExecEntrySourceLedger b β p regularWeight variableWeight) :
    L.noForbiddenShortcutStatus =
      SM3fqNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  L.noForbiddenShortcutStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
