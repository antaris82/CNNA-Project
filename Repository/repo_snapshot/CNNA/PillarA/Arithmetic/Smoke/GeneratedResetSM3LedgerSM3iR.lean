import CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

structure GeneratedResetSM3LedgerSM3iR
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
  sourcePartition : GeneratedBoundaryInteriorPartition Cell p A
  sourcePartition_eq_current : sourcePartition = P
  sourceDirichletEntrySource : GeneratedDirichletEntrySource Cell p A P wp
  sourceInteriorBlockProfile : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  sourceInteriorEliminationCertificate :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H
  sourceTwoSidedInv :
    TwoSidedInv (generatedInteriorBlock W) sourceInteriorEliminationCertificate.inverseMatrix
  sourceTopBoundaryDtN : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H
  sourceGeneralizedTopBoundaryDtN :
    GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H
  topBoundary_sourceCertificate_eq_certificate :
    sourceTopBoundaryDtN.sourceCertificate = sourceInteriorEliminationCertificate
  generalized_sourceTopBoundary_eq_topBoundary :
    sourceGeneralizedTopBoundaryDtN.sourceTopBoundaryDtN = sourceTopBoundaryDtN
  generalized_boundaryOperator_eq_topBoundary :
    sourceGeneralizedTopBoundaryDtN.boundaryOperator = sourceTopBoundaryDtN.boundaryOperator
  topBoundary_boundaryOperator_eq_certificate :
    sourceTopBoundaryDtN.boundaryOperator = sourceInteriorEliminationCertificate.boundaryOperator
  topBoundary_boundaryOperator_eq_schur :
    sourceTopBoundaryDtN.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  certificate_inverseMatrix_eq_handoffCandidate :
    sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix
  certificate_boundaryOperator_eq_schur :
    sourceInteriorEliminationCertificate.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          sourceInteriorEliminationCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  sourceInteriorBlockProfile_from_dirichlet :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorBlock W i j =
        generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j)
  noExternalDtN_from_generalized :
    sourceGeneralizedTopBoundaryDtN.noExternalDtNStatus =
      SM3hRNoExternalDtNStatus.noExternalDtNSourceInSM3hR
  noMultiSchur_from_generalized :
    sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR
  noArithmeticTarget_from_generalized :
    sourceGeneralizedTopBoundaryDtN.noArithmeticTargetStatus =
      SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR

namespace GeneratedResetSM3LedgerSM3iR

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

def fromGeneralizedTopBoundaryDtN
    (D : GeneratedDirichletEntrySource Cell p A P wp)
    (B : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H where
  sourcePartition := P
  sourcePartition_eq_current := by
    rfl
  sourceDirichletEntrySource := D
  sourceInteriorBlockProfile := B
  sourceInteriorEliminationCertificate := G.sourceTopBoundaryDtN.sourceCertificate
  sourceTwoSidedInv := G.sourceTopBoundaryDtN.sourceCertificate.inverseWitness
  sourceTopBoundaryDtN := G.sourceTopBoundaryDtN
  sourceGeneralizedTopBoundaryDtN := G
  topBoundary_sourceCertificate_eq_certificate := by
    rfl
  generalized_sourceTopBoundary_eq_topBoundary := by
    rfl
  generalized_boundaryOperator_eq_topBoundary := by
    exact G.boundaryOperator_eq_SM3gR
  topBoundary_boundaryOperator_eq_certificate := by
    exact G.sourceTopBoundaryDtN.boundaryOperator_eq_SM3fR
  topBoundary_boundaryOperator_eq_schur := by
    exact G.sourceTopBoundaryDtN.boundaryOperator_eq_schur
  certificate_inverseMatrix_eq_handoffCandidate := by
    exact G.sourceTopBoundaryDtN.sourceCertificate.inverseMatrix_eq_handoffCandidate
  certificate_boundaryOperator_eq_schur := by
    exact G.sourceTopBoundaryDtN.sourceCertificate.boundaryOperator_eq_schur
  sourceInteriorBlockProfile_from_dirichlet := by
    intro i j
    exact B.block_from_dirichlet i j
  noExternalDtN_from_generalized := by
    exact G.noExternalDtNStatus_eq
  noMultiSchur_from_generalized := by
    exact G.noMultiSchurStatus_eq
  noArithmeticTarget_from_generalized := by
    exact G.noArithmeticTargetStatus_eq

theorem generalized_boundaryOperator_from_topBoundary
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    L.sourceGeneralizedTopBoundaryDtN.boundaryOperator = L.sourceTopBoundaryDtN.boundaryOperator :=
  L.generalized_boundaryOperator_eq_topBoundary

theorem topBoundary_boundaryOperator_from_certificate
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    L.sourceTopBoundaryDtN.boundaryOperator =
      L.sourceInteriorEliminationCertificate.boundaryOperator :=
  L.topBoundary_boundaryOperator_eq_certificate

theorem certificate_inverseMatrix_from_handoffCandidate
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    L.sourceInteriorEliminationCertificate.inverseMatrix = H.candidateMatrix :=
  L.certificate_inverseMatrix_eq_handoffCandidate

theorem generalized_noMultiSchur
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    L.sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR :=
  L.noMultiSchur_from_generalized

theorem generalized_noArithmeticTarget
    (L : GeneratedResetSM3LedgerSM3iR Cell p A P wp W E K T M S H) :
    L.sourceGeneralizedTopBoundaryDtN.noArithmeticTargetStatus =
      SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR :=
  L.noArithmeticTarget_from_generalized

end GeneratedResetSM3LedgerSM3iR

def regularGeneratedResetSM3Ledger_from_accumulatedEntryCancellationLedgerSM3iR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedResetSM3LedgerSM3iR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedResetSM3LedgerSM3iR.fromGeneralizedTopBoundaryDtN
    (regularGeneratedDirichletEntrySource b p regularWeight)
    (regularGeneratedInteriorBlockStructureProfile b p regularWeight)
    (regularGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR L)

def variableGeneratedResetSM3Ledger_from_accumulatedEntryCancellationLedgerSM3iR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedResetSM3LedgerSM3iR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedResetSM3LedgerSM3iR.fromGeneralizedTopBoundaryDtN
    (variableGeneratedDirichletEntrySource β p variableWeight)
    (variableGeneratedInteriorBlockStructureProfile β p variableWeight)
    (variableGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR L)

structure SM3iRGeneratedResetLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceAccumulatedEntryCancellationLedger :
    SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight
  sourceSM3aPartitionLedger : SM3aRGeneratedPartitionLedger b β p
  sourceSM3bDirichletEntryLedger :
    SM3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  sourceSM3cInteriorBlockLedger :
    SM3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight
  regularLedger :
    GeneratedResetSM3LedgerSM3iR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableLedger :
    GeneratedResetSM3LedgerSM3iR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  sourceSM3aPartitionLedger_eq_main :
    sourceSM3aPartitionLedger = sm3aRGeneratedPartitionLedger b β p
  sourceSM3bDirichletEntryLedger_eq_main :
    sourceSM3bDirichletEntryLedger =
      sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  sourceSM3cInteriorBlockLedger_eq_main :
    sourceSM3cInteriorBlockLedger =
      sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight
  regularInteriorEliminationCertificate_eq_SM3fR :
    regularLedger.sourceInteriorEliminationCertificate =
      regularGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
        sourceAccumulatedEntryCancellationLedger
  variableInteriorEliminationCertificate_eq_SM3fR :
    variableLedger.sourceInteriorEliminationCertificate =
      variableGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
        sourceAccumulatedEntryCancellationLedger
  regularTopBoundaryDtN_eq_SM3gR :
    regularLedger.sourceTopBoundaryDtN =
      regularGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR
        sourceAccumulatedEntryCancellationLedger
  variableTopBoundaryDtN_eq_SM3gR :
    variableLedger.sourceTopBoundaryDtN =
      variableGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR
        sourceAccumulatedEntryCancellationLedger
  regularGeneralizedTopBoundaryDtN_eq_SM3hR :
    regularLedger.sourceGeneralizedTopBoundaryDtN =
      regularGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR
        sourceAccumulatedEntryCancellationLedger
  variableGeneralizedTopBoundaryDtN_eq_SM3hR :
    variableLedger.sourceGeneralizedTopBoundaryDtN =
      variableGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR
        sourceAccumulatedEntryCancellationLedger
  regularNoMultiSchur :
    regularLedger.sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR
  variableNoMultiSchur :
    variableLedger.sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR
  regularNoArithmeticTarget :
    regularLedger.sourceGeneralizedTopBoundaryDtN.noArithmeticTargetStatus =
      SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR
  variableNoArithmeticTarget :
    variableLedger.sourceGeneralizedTopBoundaryDtN.noArithmeticTargetStatus =
      SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR

def sm3iRGeneratedResetLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM3iRGeneratedResetLedger b β p regularWeight variableWeight where
  sourceAccumulatedEntryCancellationLedger := L
  sourceSM3aPartitionLedger := sm3aRGeneratedPartitionLedger b β p
  sourceSM3bDirichletEntryLedger :=
    sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  sourceSM3cInteriorBlockLedger :=
    sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight
  regularLedger :=
    regularGeneratedResetSM3Ledger_from_accumulatedEntryCancellationLedgerSM3iR L
  variableLedger :=
    variableGeneratedResetSM3Ledger_from_accumulatedEntryCancellationLedgerSM3iR L
  sourceSM3aPartitionLedger_eq_main := by
    rfl
  sourceSM3bDirichletEntryLedger_eq_main := by
    rfl
  sourceSM3cInteriorBlockLedger_eq_main := by
    rfl
  regularInteriorEliminationCertificate_eq_SM3fR := by
    rfl
  variableInteriorEliminationCertificate_eq_SM3fR := by
    rfl
  regularTopBoundaryDtN_eq_SM3gR := by
    rfl
  variableTopBoundaryDtN_eq_SM3gR := by
    rfl
  regularGeneralizedTopBoundaryDtN_eq_SM3hR := by
    rfl
  variableGeneralizedTopBoundaryDtN_eq_SM3hR := by
    rfl
  regularNoMultiSchur := by
    rfl
  variableNoMultiSchur := by
    rfl
  regularNoArithmeticTarget := by
    rfl
  variableNoArithmeticTarget := by
    rfl

theorem sm3iRGeneratedResetLedger_regular_noMultiSchur
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    L.regularLedger.sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR :=
  L.regularNoMultiSchur

theorem sm3iRGeneratedResetLedger_variable_noMultiSchur
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    L.variableLedger.sourceGeneralizedTopBoundaryDtN.noMultiSchurStatus =
      SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR :=
  L.variableNoMultiSchur

theorem sm3iRGeneratedResetLedger_regular_certificate_from_SM3fR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    L.regularLedger.sourceInteriorEliminationCertificate =
      regularGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
        L.sourceAccumulatedEntryCancellationLedger :=
  L.regularInteriorEliminationCertificate_eq_SM3fR

theorem sm3iRGeneratedResetLedger_variable_certificate_from_SM3fR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3iRGeneratedResetLedger b β p regularWeight variableWeight) :
    L.variableLedger.sourceInteriorEliminationCertificate =
      variableGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
        L.sourceAccumulatedEntryCancellationLedger :=
  L.variableInteriorEliminationCertificate_eq_SM3fR

end Smoke

end CNNA.PillarA.Arithmetic
