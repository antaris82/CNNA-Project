import CNNA.PillarA.Foundation.ExecComplexBridge
import CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM4qBoundaryOperatorProvenanceStatus where
  | realBoundaryOperatorIsSM4SM3iRSM3fSchur
  deriving DecidableEq, Repr

inductive SM4qExecBoundaryOperatorConstructionStatus where
  | blockedMissingSM3fSM3eRExecSchurEntrySource
  deriving DecidableEq, Repr

inductive SM4qMissingExecSourceStatus where
  | missingOperationalSchurEntryAndInverseMatrixBridge
  deriving DecidableEq, Repr

inductive SM4qNextPhaseStatus where
  | sm3fSM3eRGeneratedExecSchurEntrySource
  deriving DecidableEq, Repr

inductive SM4qNoForbiddenShortcutStatus where
  | noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  deriving DecidableEq, Repr

structure GeneratedMultiSchurExecBoundaryOperatorWitnessSM4q
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
  sourceSM4 : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM4 : boundaryOperatorReal = sourceSM4.boundaryOperator
  execBoundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  exec_entry_bridge : ∀ i j,
    ExecComplexBridge.toComplex (execBoundaryOperator i j) =
      (sourceSM4.boundaryOperator i j : ℂ)
  entry_eq_SM3iR : ∀ i j,
    boundaryOperatorReal i j =
      sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator i j
  entry_eq_topBoundary : ∀ i j,
    boundaryOperatorReal i j = sourceSM4.sourceTopBoundaryDtN.boundaryOperator i j
  entry_eq_certificate : ∀ i j,
    boundaryOperatorReal i j =
      sourceSM4.sourceInteriorEliminationCertificate.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  certificate_inverseMatrix_eq_handoffCandidate :
    sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix
  provenanceStatus : SM4qBoundaryOperatorProvenanceStatus
  provenanceStatus_eq :
    provenanceStatus =
      SM4qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM4SM3iRSM3fSchur

structure GeneratedMultiSchurExecBoundaryOperatorSM4q
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
  sourceSM4 : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H
  boundaryOperatorReal : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperatorReal_eq_SM4 : boundaryOperatorReal = sourceSM4.boundaryOperator
  entry_eq_SM3iR : ∀ i j,
    boundaryOperatorReal i j =
      sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator i j
  entry_eq_topBoundary : ∀ i j,
    boundaryOperatorReal i j = sourceSM4.sourceTopBoundaryDtN.boundaryOperator i j
  entry_eq_certificate : ∀ i j,
    boundaryOperatorReal i j =
      sourceSM4.sourceInteriorEliminationCertificate.boundaryOperator i j
  entry_eq_schur : ∀ i j,
    boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j
  apply_eq_SM3iR : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM4.«apply» φ =
      sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    sourceSM4.«apply» φ = boundaryOperatorReal.mulVec φ
  certificate_inverseMatrix_eq_handoffCandidate :
    sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix
  provenanceStatus : SM4qBoundaryOperatorProvenanceStatus
  provenanceStatus_eq :
    provenanceStatus =
      SM4qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM4SM3iRSM3fSchur
  execBoundaryOperatorConstructionStatus : SM4qExecBoundaryOperatorConstructionStatus
  execBoundaryOperatorConstructionStatus_eq :
    execBoundaryOperatorConstructionStatus =
      SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource
  missingExecSourceStatus : SM4qMissingExecSourceStatus
  missingExecSourceStatus_eq :
    missingExecSourceStatus =
      SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge
  nextPhaseStatus : SM4qNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM4qNextPhaseStatus.sm3fSM3eRGeneratedExecSchurEntrySource
  noForbiddenShortcutStatus : SM4qNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM4qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

namespace GeneratedMultiSchurExecBoundaryOperatorSM4q

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

def fromSM4
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H where
  sourceSM4 := G
  boundaryOperatorReal := G.boundaryOperator
  boundaryOperatorReal_eq_SM4 := by
    rfl
  entry_eq_SM3iR := by
    intro i j
    exact congrArg (fun M => M i j) G.boundaryOperator_eq_SM3iR
  entry_eq_topBoundary := by
    intro i j
    exact congrArg (fun M => M i j) G.boundaryOperator_eq_topBoundary
  entry_eq_certificate := by
    intro i j
    exact congrArg (fun M => M i j) G.boundaryOperator_eq_certificate
  entry_eq_schur := by
    intro i j
    exact congrArg (fun M => M i j) G.boundaryOperator_eq_schur
  apply_eq_SM3iR := by
    intro φ
    exact G.apply_eq_SM3iR φ
  apply_eq_mulVec := by
    intro φ
    exact G.apply_eq_mulVec φ
  certificate_inverseMatrix_eq_handoffCandidate := by
    exact G.certificate_inverseMatrix_eq_handoffCandidate
  provenanceStatus :=
    SM4qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM4SM3iRSM3fSchur
  provenanceStatus_eq := by
    rfl
  execBoundaryOperatorConstructionStatus :=
    SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource
  execBoundaryOperatorConstructionStatus_eq := by
    rfl
  missingExecSourceStatus :=
    SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge
  missingExecSourceStatus_eq := by
    rfl
  nextPhaseStatus := SM4qNextPhaseStatus.sm3fSM3eRGeneratedExecSchurEntrySource
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM4qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem boundaryOperatorReal_from_SM4
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.boundaryOperatorReal = X.sourceSM4.boundaryOperator :=
  X.boundaryOperatorReal_eq_SM4

theorem entryReal_from_SM3iR
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      X.sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator i j :=
  X.entry_eq_SM3iR i j

theorem entryReal_from_topBoundary
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j = X.sourceSM4.sourceTopBoundaryDtN.boundaryOperator i j :=
  X.entry_eq_topBoundary i j

theorem entryReal_from_certificate
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      X.sourceSM4.sourceInteriorEliminationCertificate.boundaryOperator i j :=
  X.entry_eq_certificate i j

theorem entryReal_from_schur
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    X.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          X.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j :=
  X.entry_eq_schur i j

theorem apply_from_SM3iR
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM4.«apply» φ =
      X.sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.«apply» φ :=
  X.apply_eq_SM3iR φ

theorem apply_from_boundaryOperatorReal_mulVec
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    X.sourceSM4.«apply» φ = X.boundaryOperatorReal.mulVec φ :=
  X.apply_eq_mulVec φ

theorem certificate_inverseMatrix_from_handoffCandidate
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix :=
  X.certificate_inverseMatrix_eq_handoffCandidate

theorem provenance_is_SM4_SM3iR_SM3f_schur
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.provenanceStatus =
      SM4qBoundaryOperatorProvenanceStatus.realBoundaryOperatorIsSM4SM3iRSM3fSchur :=
  X.provenanceStatus_eq

theorem execBoundaryOperator_blocked_missing_SM3f_SM3eR_source
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.execBoundaryOperatorConstructionStatus =
      SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource :=
  X.execBoundaryOperatorConstructionStatus_eq

theorem missing_exec_source_is_operational_schur_bridge
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.missingExecSourceStatus =
      SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge :=
  X.missingExecSourceStatus_eq

theorem nextPhase_is_SM3f_SM3eR_exec_schur_source
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.nextPhaseStatus = SM4qNextPhaseStatus.sm3fSM3eRGeneratedExecSchurEntrySource :=
  X.nextPhaseStatus_eq

theorem noForbiddenShortcuts_for_SM4q
    (X : GeneratedMultiSchurExecBoundaryOperatorSM4q Cell p A P wp W E K T M S H) :
    X.noForbiddenShortcutStatus =
      SM4qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  X.noForbiddenShortcutStatus_eq

end GeneratedMultiSchurExecBoundaryOperatorSM4q

def regularGeneratedMultiSchurExecBoundaryOperatorSM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    GeneratedMultiSchurExecBoundaryOperatorSM4q
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedMultiSchurExecBoundaryOperatorSM4q.fromSM4 L.regularMultiSchur

def variableGeneratedMultiSchurExecBoundaryOperatorSM4q
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    GeneratedMultiSchurExecBoundaryOperatorSM4q
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedMultiSchurExecBoundaryOperatorSM4q.fromSM4 L.variableMultiSchur

structure SM4qGeneratedMultiSchurExecBoundaryOperatorLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM4Ledger : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight
  regularSource :
    GeneratedMultiSchurExecBoundaryOperatorSM4q
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
    GeneratedMultiSchurExecBoundaryOperatorSM4q
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularSource_eq_from_SM4 :
    regularSource = regularGeneratedMultiSchurExecBoundaryOperatorSM4q sourceSM4Ledger
  variableSource_eq_from_SM4 :
    variableSource = variableGeneratedMultiSchurExecBoundaryOperatorSM4q sourceSM4Ledger
  regular_entry_eq_SM3iR : ∀ i j,
    regularSource.boundaryOperatorReal i j =
      regularSource.sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator i j
  variable_entry_eq_SM3iR : ∀ i j,
    variableSource.boundaryOperatorReal i j =
      variableSource.sourceSM4.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator i j
  regular_entry_eq_schur : ∀ i j,
    regularSource.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR
        (regularGeneratedWeightPolicyEntrySource b p regularWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (regularGeneratedWeightPolicyEntrySource b p regularWeight) *
          regularSource.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (regularGeneratedWeightPolicyEntrySource b p regularWeight)) i j
  variable_entry_eq_schur : ∀ i j,
    variableSource.boundaryOperatorReal i j =
      (generatedBoundaryBlockSM3fR
        (variableGeneratedWeightPolicyEntrySource β p variableWeight) -
        generatedBoundaryInteriorBlockSM3fR
          (variableGeneratedWeightPolicyEntrySource β p variableWeight) *
          variableSource.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR
            (variableGeneratedWeightPolicyEntrySource β p variableWeight)) i j
  regular_certificate_inverseMatrix_eq_handoffCandidate :
    regularSource.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix =
      (regularSM3dbRToSM3eRHandoff b p regularWeight).candidateMatrix
  variable_certificate_inverseMatrix_eq_handoffCandidate :
    variableSource.sourceSM4.sourceInteriorEliminationCertificate.inverseMatrix =
      (variableSM3dbRToSM3eRHandoff β p variableWeight).candidateMatrix
  regularConstructionStatus : SM4qExecBoundaryOperatorConstructionStatus
  regularConstructionStatus_eq :
    regularConstructionStatus =
      SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource
  variableConstructionStatus : SM4qExecBoundaryOperatorConstructionStatus
  variableConstructionStatus_eq :
    variableConstructionStatus =
      SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource
  regularMissingSourceStatus : SM4qMissingExecSourceStatus
  regularMissingSourceStatus_eq :
    regularMissingSourceStatus =
      SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge
  variableMissingSourceStatus : SM4qMissingExecSourceStatus
  variableMissingSourceStatus_eq :
    variableMissingSourceStatus =
      SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge
  nextPhaseStatus : SM4qNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM4qNextPhaseStatus.sm3fSM3eRGeneratedExecSchurEntrySource
  noForbiddenShortcutStatus : SM4qNoForbiddenShortcutStatus
  noForbiddenShortcutStatus_eq :
    noForbiddenShortcutStatus =
      SM4qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner

def sm4qGeneratedMultiSchurExecBoundaryOperatorLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    SM4qGeneratedMultiSchurExecBoundaryOperatorLedger b β p regularWeight variableWeight where
  sourceSM4Ledger := L
  regularSource := regularGeneratedMultiSchurExecBoundaryOperatorSM4q L
  variableSource := variableGeneratedMultiSchurExecBoundaryOperatorSM4q L
  regularSource_eq_from_SM4 := by
    rfl
  variableSource_eq_from_SM4 := by
    rfl
  regular_entry_eq_SM3iR := by
    intro i j
    exact (regularGeneratedMultiSchurExecBoundaryOperatorSM4q L).entry_eq_SM3iR i j
  variable_entry_eq_SM3iR := by
    intro i j
    exact (variableGeneratedMultiSchurExecBoundaryOperatorSM4q L).entry_eq_SM3iR i j
  regular_entry_eq_schur := by
    intro i j
    exact (regularGeneratedMultiSchurExecBoundaryOperatorSM4q L).entry_eq_schur i j
  variable_entry_eq_schur := by
    intro i j
    exact (variableGeneratedMultiSchurExecBoundaryOperatorSM4q L).entry_eq_schur i j
  regular_certificate_inverseMatrix_eq_handoffCandidate := by
    exact (regularGeneratedMultiSchurExecBoundaryOperatorSM4q L).certificate_inverseMatrix_eq_handoffCandidate
  variable_certificate_inverseMatrix_eq_handoffCandidate := by
    exact (variableGeneratedMultiSchurExecBoundaryOperatorSM4q L).certificate_inverseMatrix_eq_handoffCandidate
  regularConstructionStatus :=
    SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource
  regularConstructionStatus_eq := by
    rfl
  variableConstructionStatus :=
    SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource
  variableConstructionStatus_eq := by
    rfl
  regularMissingSourceStatus :=
    SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge
  regularMissingSourceStatus_eq := by
    rfl
  variableMissingSourceStatus :=
    SM4qMissingExecSourceStatus.missingOperationalSchurEntryAndInverseMatrixBridge
  variableMissingSourceStatus_eq := by
    rfl
  nextPhaseStatus := SM4qNextPhaseStatus.sm3fSM3eRGeneratedExecSchurEntrySource
  nextPhaseStatus_eq := by
    rfl
  noForbiddenShortcutStatus :=
    SM4qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner
  noForbiddenShortcutStatus_eq := by
    rfl

theorem sm4q_regularConstruction_blocked_missing_SM3f_SM3eR_source
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qGeneratedMultiSchurExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.regularConstructionStatus =
      SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource :=
  L.regularConstructionStatus_eq

theorem sm4q_variableConstruction_blocked_missing_SM3f_SM3eR_source
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qGeneratedMultiSchurExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.variableConstructionStatus =
      SM4qExecBoundaryOperatorConstructionStatus.blockedMissingSM3fSM3eRExecSchurEntrySource :=
  L.variableConstructionStatus_eq

theorem sm4q_nextPhase_is_SM3f_SM3eR_exec_schur_source
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qGeneratedMultiSchurExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM4qNextPhaseStatus.sm3fSM3eRGeneratedExecSchurEntrySource :=
  L.nextPhaseStatus_eq

theorem sm4q_noForbiddenShortcuts
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4qGeneratedMultiSchurExecBoundaryOperatorLedger b β p regularWeight variableWeight) :
    L.noForbiddenShortcutStatus =
      SM4qNoForbiddenShortcutStatus.noFreeExecNoRealToRatNoScalarInvNoMatrixInvNoFieldSimpNoCharpolyNoHeegner :=
  L.noForbiddenShortcutStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
