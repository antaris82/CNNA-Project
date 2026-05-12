import CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM4GeneratedMultiSchurSourceStatus where
  | generatedLocallyFromSM3iRResetLedger
  deriving DecidableEq, Repr

inductive SM4NoPublicMultiSchurStrongStatus where
  | noPublicMultiSchurStrongForcedInSM4
  deriving DecidableEq, Repr

inductive SM4NoForbiddenArithmeticTargetStatus where
  | noArithmeticSourceLevelHistoryCharpolyFactorDiscriminantInSM4
  deriving DecidableEq, Repr

def generatedMultiSchurBoundaryOperatorSM4
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ :=
  L.sourceGeneralizedTopBoundaryDtN.boundaryOperator

def generatedMultiSchurApplySM4
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    GeneratedBoundaryIndex A → ℝ :=
  L.sourceGeneralizedTopBoundaryDtN.«apply» φ

structure GeneratedMultiSchurSM4
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
  sourceResetLedger : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H
  sourceStatus : SM4GeneratedMultiSchurSourceStatus
  sourceStatus_eq_SM3iR :
    sourceStatus = SM4GeneratedMultiSchurSourceStatus.generatedLocallyFromSM3iRResetLedger
  sourceGeneralizedTopBoundaryDtN :
    GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H
  sourceGeneralizedTopBoundaryDtN_eq_SM3iR :
    sourceGeneralizedTopBoundaryDtN = sourceResetLedger.sourceGeneralizedTopBoundaryDtN
  sourceTopBoundaryDtN : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H
  sourceTopBoundaryDtN_eq_SM3iR :
    sourceTopBoundaryDtN = sourceResetLedger.sourceTopBoundaryDtN
  sourceInteriorEliminationCertificate :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H
  sourceInteriorEliminationCertificate_eq_SM3iR :
    sourceInteriorEliminationCertificate = sourceResetLedger.sourceInteriorEliminationCertificate
  sourceInteriorEliminationCertificate_eq_topBoundary :
    sourceInteriorEliminationCertificate = sourceTopBoundaryDtN.sourceCertificate
  boundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperator_eq_SM3iR :
    boundaryOperator = sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator
  boundaryOperator_eq_topBoundary :
    boundaryOperator = sourceTopBoundaryDtN.boundaryOperator
  boundaryOperator_eq_certificate :
    boundaryOperator = sourceInteriorEliminationCertificate.boundaryOperator
  boundaryOperator_eq_schur :
    boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  «apply» : (GeneratedBoundaryIndex A → ℝ) → GeneratedBoundaryIndex A → ℝ
  apply_eq_SM3iR : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = sourceResetLedger.sourceGeneralizedTopBoundaryDtN.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = boundaryOperator.mulVec φ
  certificate_inverseMatrix_eq_handoffCandidate :
    sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix
  noExternalDtN_from_SM3iR :
    sourceGeneralizedTopBoundaryDtN.noExternalDtNStatus =
      SM3hRNoExternalDtNStatus.noExternalDtNSourceInSM3hR
  sourceGeneralized_noMultiSchur_before_SM4 :
    sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR
  noPublicMultiSchurStrongStatus : SM4NoPublicMultiSchurStrongStatus
  noPublicMultiSchurStrongStatus_eq :
    noPublicMultiSchurStrongStatus =
      SM4NoPublicMultiSchurStrongStatus.noPublicMultiSchurStrongForcedInSM4
  noForbiddenArithmeticTargetStatus : SM4NoForbiddenArithmeticTargetStatus
  noForbiddenArithmeticTargetStatus_eq :
    noForbiddenArithmeticTargetStatus =
      SM4NoForbiddenArithmeticTargetStatus.noArithmeticSourceLevelHistoryCharpolyFactorDiscriminantInSM4

namespace GeneratedMultiSchurSM4

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

def fromSM3iR
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H where
  sourceResetLedger := L
  sourceStatus := SM4GeneratedMultiSchurSourceStatus.generatedLocallyFromSM3iRResetLedger
  sourceStatus_eq_SM3iR := by
    rfl
  sourceGeneralizedTopBoundaryDtN := L.sourceGeneralizedTopBoundaryDtN
  sourceGeneralizedTopBoundaryDtN_eq_SM3iR := by
    rfl
  sourceTopBoundaryDtN := L.sourceTopBoundaryDtN
  sourceTopBoundaryDtN_eq_SM3iR := by
    rfl
  sourceInteriorEliminationCertificate := L.sourceInteriorEliminationCertificate
  sourceInteriorEliminationCertificate_eq_SM3iR := by
    rfl
  sourceInteriorEliminationCertificate_eq_topBoundary := by
    exact L.topBoundary_sourceCertificate_eq_certificate.symm
  boundaryOperator := generatedMultiSchurBoundaryOperatorSM4 L
  boundaryOperator_eq_SM3iR := by
    rfl
  boundaryOperator_eq_topBoundary := by
    exact L.generalized_boundaryOperator_eq_topBoundary
  boundaryOperator_eq_certificate := by
    calc
      L.sourceGeneralizedTopBoundaryDtN.boundaryOperator = L.sourceTopBoundaryDtN.boundaryOperator :=
        L.generalized_boundaryOperator_eq_topBoundary
      _ = L.sourceInteriorEliminationCertificate.boundaryOperator :=
        L.topBoundary_boundaryOperator_eq_certificate
  boundaryOperator_eq_schur := by
    calc
      L.sourceGeneralizedTopBoundaryDtN.boundaryOperator = L.sourceTopBoundaryDtN.boundaryOperator :=
        L.generalized_boundaryOperator_eq_topBoundary
      _ = L.sourceInteriorEliminationCertificate.boundaryOperator :=
        L.topBoundary_boundaryOperator_eq_certificate
      _ = generatedBoundaryBlockSM3fR W -
            generatedBoundaryInteriorBlockSM3fR W *
              L.sourceInteriorEliminationCertificate.inverseMatrix *
              generatedInteriorBoundaryBlockSM3fR W :=
        L.certificate_boundaryOperator_eq_schur
  «apply» := generatedMultiSchurApplySM4 L
  apply_eq_SM3iR := by
    intro φ
    rfl
  apply_eq_mulVec := by
    intro φ
    exact L.sourceGeneralizedTopBoundaryDtN.apply_eq_mulVec φ
  certificate_inverseMatrix_eq_handoffCandidate := by
    exact L.certificate_inverseMatrix_eq_handoffCandidate
  noExternalDtN_from_SM3iR := by
    exact L.noExternalDtN_from_generalized
  sourceGeneralized_noMultiSchur_before_SM4 := by
    exact L.noMultiSchur_from_generalized
  noPublicMultiSchurStrongStatus :=
    SM4NoPublicMultiSchurStrongStatus.noPublicMultiSchurStrongForcedInSM4
  noPublicMultiSchurStrongStatus_eq := by
    rfl
  noForbiddenArithmeticTargetStatus :=
    SM4NoForbiddenArithmeticTargetStatus.noArithmeticSourceLevelHistoryCharpolyFactorDiscriminantInSM4
  noForbiddenArithmeticTargetStatus_eq := by
    rfl

theorem source_from_SM3iR
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.sourceStatus = SM4GeneratedMultiSchurSourceStatus.generatedLocallyFromSM3iRResetLedger :=
  G.sourceStatus_eq_SM3iR

theorem boundaryOperator_from_SM3iR
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.boundaryOperator = G.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator :=
  G.boundaryOperator_eq_SM3iR

theorem boundaryOperator_from_topBoundary
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.boundaryOperator = G.sourceTopBoundaryDtN.boundaryOperator :=
  G.boundaryOperator_eq_topBoundary

theorem boundaryOperator_from_certificate
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.boundaryOperator = G.sourceInteriorEliminationCertificate.boundaryOperator :=
  G.boundaryOperator_eq_certificate

theorem boundaryOperator_from_schur
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          G.sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  G.boundaryOperator_eq_schur

theorem apply_from_SM3iR
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    G.«apply» φ = G.sourceResetLedger.sourceGeneralizedTopBoundaryDtN.«apply» φ :=
  G.apply_eq_SM3iR φ

theorem apply_from_mulVec
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    G.«apply» φ = G.boundaryOperator.mulVec φ :=
  G.apply_eq_mulVec φ

theorem certificate_inverseMatrix_from_handoffCandidate
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix :=
  G.certificate_inverseMatrix_eq_handoffCandidate

theorem noExternalDtN_status_from_SM3iR
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.sourceGeneralizedTopBoundaryDtN.noExternalDtNStatus =
      SM3hRNoExternalDtNStatus.noExternalDtNSourceInSM3hR :=
  G.noExternalDtN_from_SM3iR

theorem sourceGeneralized_noMultiSchur_status_before_SM4
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR :=
  G.sourceGeneralized_noMultiSchur_before_SM4

theorem noPublicMultiSchurStrong_for_SM4
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.noPublicMultiSchurStrongStatus =
      SM4NoPublicMultiSchurStrongStatus.noPublicMultiSchurStrongForcedInSM4 :=
  G.noPublicMultiSchurStrongStatus_eq

theorem noForbiddenArithmeticTarget_for_SM4
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) :
    G.noForbiddenArithmeticTargetStatus =
      SM4NoForbiddenArithmeticTargetStatus.noArithmeticSourceLevelHistoryCharpolyFactorDiscriminantInSM4 :=
  G.noForbiddenArithmeticTargetStatus_eq

end GeneratedMultiSchurSM4

def generatedMultiSchur_from_SM3iRSM4
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H :=
  GeneratedMultiSchurSM4.fromSM3iR L

def regularGeneratedMultiSchur_from_SM3iRSM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    GeneratedMultiSchurSM4
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  generatedMultiSchur_from_SM3iRSM4 L.regularLedger

def variableGeneratedMultiSchur_from_SM3iRSM4
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    GeneratedMultiSchurSM4
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  generatedMultiSchur_from_SM3iRSM4 L.variableLedger

structure SM4GeneratedMultiSchurLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM3iRLedger : SM3iRGeneratedResetLedger b β p regularWeight variableWeight
  regularMultiSchur :
    GeneratedMultiSchurSM4
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableMultiSchur :
    GeneratedMultiSchurSM4
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regular_from_SM3iR :
    regularMultiSchur = regularGeneratedMultiSchur_from_SM3iRSM4 sourceSM3iRLedger
  variable_from_SM3iR :
    variableMultiSchur = variableGeneratedMultiSchur_from_SM3iRSM4 sourceSM3iRLedger
  regular_certificate_from_SM3fR :
    regularMultiSchur.sourceInteriorEliminationCertificate =
      regularGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
        sourceSM3iRLedger.sourceAccumulatedEntryCancellationLedger
  variable_certificate_from_SM3fR :
    variableMultiSchur.sourceInteriorEliminationCertificate =
      variableGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
        sourceSM3iRLedger.sourceAccumulatedEntryCancellationLedger
  regular_topBoundaryDtN_from_SM3gR :
    regularMultiSchur.sourceTopBoundaryDtN =
      regularGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR
        sourceSM3iRLedger.sourceAccumulatedEntryCancellationLedger
  variable_topBoundaryDtN_from_SM3gR :
    variableMultiSchur.sourceTopBoundaryDtN =
      variableGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR
        sourceSM3iRLedger.sourceAccumulatedEntryCancellationLedger
  regular_generalizedTopBoundaryDtN_from_SM3hR :
    regularMultiSchur.sourceGeneralizedTopBoundaryDtN =
      regularGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR
        sourceSM3iRLedger.sourceAccumulatedEntryCancellationLedger
  variable_generalizedTopBoundaryDtN_from_SM3hR :
    variableMultiSchur.sourceGeneralizedTopBoundaryDtN =
      variableGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR
        sourceSM3iRLedger.sourceAccumulatedEntryCancellationLedger
  regular_noPublicMultiSchurStrong :
    regularMultiSchur.noPublicMultiSchurStrongStatus =
      SM4NoPublicMultiSchurStrongStatus.noPublicMultiSchurStrongForcedInSM4
  variable_noPublicMultiSchurStrong :
    variableMultiSchur.noPublicMultiSchurStrongStatus =
      SM4NoPublicMultiSchurStrongStatus.noPublicMultiSchurStrongForcedInSM4
  regular_noForbiddenArithmeticTarget :
    regularMultiSchur.noForbiddenArithmeticTargetStatus =
      SM4NoForbiddenArithmeticTargetStatus.noArithmeticSourceLevelHistoryCharpolyFactorDiscriminantInSM4
  variable_noForbiddenArithmeticTarget :
    variableMultiSchur.noForbiddenArithmeticTargetStatus =
      SM4NoForbiddenArithmeticTargetStatus.noArithmeticSourceLevelHistoryCharpolyFactorDiscriminantInSM4

def sm4GeneratedMultiSchurLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight where
  sourceSM3iRLedger := L
  regularMultiSchur := regularGeneratedMultiSchur_from_SM3iRSM4 L
  variableMultiSchur := variableGeneratedMultiSchur_from_SM3iRSM4 L
  regular_from_SM3iR := by
    rfl
  variable_from_SM3iR := by
    rfl
  regular_certificate_from_SM3fR := by
    exact L.regularInteriorEliminationCertificate_eq_SM3fR
  variable_certificate_from_SM3fR := by
    exact L.variableInteriorEliminationCertificate_eq_SM3fR
  regular_topBoundaryDtN_from_SM3gR := by
    exact L.regularTopBoundaryDtN_eq_SM3gR
  variable_topBoundaryDtN_from_SM3gR := by
    exact L.variableTopBoundaryDtN_eq_SM3gR
  regular_generalizedTopBoundaryDtN_from_SM3hR := by
    exact L.regularGeneralizedTopBoundaryDtN_eq_SM3hR
  variable_generalizedTopBoundaryDtN_from_SM3hR := by
    exact L.variableGeneralizedTopBoundaryDtN_eq_SM3hR
  regular_noPublicMultiSchurStrong := by
    rfl
  variable_noPublicMultiSchurStrong := by
    rfl
  regular_noForbiddenArithmeticTarget := by
    rfl
  variable_noForbiddenArithmeticTarget := by
    rfl

def sm4GeneratedMultiSchurLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight :=
  sm4GeneratedMultiSchurLedger (sm3iRGeneratedResetLedger L)

theorem sm4GeneratedMultiSchurLedger_regular_boundaryOperator_from_SM3iR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    L.regularMultiSchur.boundaryOperator =
      L.sourceSM3iRLedger.regularLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator := by
  rw [L.regular_from_SM3iR]
  rfl

theorem sm4GeneratedMultiSchurLedger_variable_boundaryOperator_from_SM3iR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight) :
    L.variableMultiSchur.boundaryOperator =
      L.sourceSM3iRLedger.variableLedger.sourceGeneralizedTopBoundaryDtN.boundaryOperator := by
  rw [L.variable_from_SM3iR]
  rfl

theorem sm4GeneratedMultiSchurLedger_regular_apply_eq_mulVec
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight)
    (φ : GeneratedBoundaryIndex (regularGeneratedApproximantStrong b p) → ℝ) :
    L.regularMultiSchur.«apply» φ = L.regularMultiSchur.boundaryOperator.mulVec φ :=
  L.regularMultiSchur.apply_eq_mulVec φ

theorem sm4GeneratedMultiSchurLedger_variable_apply_eq_mulVec
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM4GeneratedMultiSchurLedger b β p regularWeight variableWeight)
    (φ : GeneratedBoundaryIndex (variableGeneratedApproximantStrong β p) → ℝ) :
    L.variableMultiSchur.«apply» φ = L.variableMultiSchur.boundaryOperator.mulVec φ :=
  L.variableMultiSchur.apply_eq_mulVec φ

end Smoke

end CNNA.PillarA.Arithmetic
