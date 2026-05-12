import CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff
import CNNA.PillarA.DtN.DtN

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

open scoped BigOperators

namespace Smoke

universe u

inductive SM3eRReRunHandoffShapeAuditStatus where
  | handoffShapeAuditedFromSM3db7R
  deriving DecidableEq, Repr

inductive SM3eRReRunLeftProductStatus where
  | leftProductFromInteriorBlockAndHandoffCandidate
  deriving DecidableEq, Repr

inductive SM3eRReRunRightProductStatus where
  | rightProductFromHandoffCandidateAndInteriorBlock
  deriving DecidableEq, Repr

inductive SM3eRReRunProductNormalFormStatus where
  | productNormalFormsFromSM3db7RHandoffAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3eRReRunTraceCancellationStatus where
  | traceCancellationFromSM3db4aRAccumulatedEntryAndR3aNormalForms
  deriving DecidableEq, Repr

inductive SM3eRReRunProductCancellationLedgerStatus where
  | productCancellationLedgerFromTraceCancellation
  deriving DecidableEq, Repr

inductive SM3eRReRunNoProductIdentityProofStatus where
  | noProductIdentityProofConstructedInR3b
  deriving DecidableEq, Repr

inductive SM3eRReRunR4GateStatus where
  | r4ReadyAfterR3bCancellationFields
  deriving DecidableEq, Repr

inductive SM3eRReRunDiagonalOffdiagStatus where
  | diagonalOffdiagGoalsProofCarrying
  deriving DecidableEq, Repr

inductive SM3eRReRunProofGateStatus where
  | waitingForLeftAndRightProductIdentityProofs
  deriving DecidableEq, Repr

inductive SM3eRReRunSM3fGateStatus where
  | sm3fBlockedUntilHandoffTwoSidedInv
  deriving DecidableEq, Repr

inductive SM3eRReRunNoSM3daRFallbackStatus where
  | noSM3daRFallbackInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoFreeEntryTableStatus where
  | noFreeEntryTableInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoMatrixInvStatus where
  | noMatrixInvInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoExternalInverseOracleStatus where
  | noExternalInverseOracleInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun
  deriving DecidableEq, Repr

inductive SM3eRReRunLedgerStatus where
  | handoffProductCalculusPrepared
  deriving DecidableEq, Repr

def GeneratedInteriorSM3db7RLeftProductEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (generatedInteriorBlock W * H.candidateMatrix) i j

def GeneratedInteriorSM3db7RRightProductEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (H.candidateMatrix * generatedInteriorBlock W) i j

theorem generatedInteriorSM3db7RLeftProductEntry_eq_matrixProduct
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
      (generatedInteriorBlock W * H.candidateMatrix) i j := by
  rfl

theorem generatedInteriorSM3db7RRightProductEntry_eq_matrixProduct
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i j =
      (H.candidateMatrix * generatedInteriorBlock W) i j := by
  rfl

structure GeneratedInteriorSM3db7RHandoffShapeAudit
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  status : SM3eRReRunHandoffShapeAuditStatus
  mayConsumeOnlyHandoff : SM3eRMayConsumeOnlySM3dbRInverseCandidate H
  noSM3daRFallbackStatus : SM3eRReRunNoSM3daRFallbackStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  noMatrixInvStatus : SM3eRReRunNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3eRReRunNoExternalInverseOracleStatus
  candidateMatrix_eq_SM3db6R_shapeSeparationMatrix : H.candidateMatrix = S.matrix
  candidateMatrixEntry_eq_SM3db5R_matrixExport :
    ∀ i j : GeneratedInteriorIndex A, H.candidateMatrix i j = M.matrix i j
  candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry :
    ∀ i j : GeneratedInteriorIndex A,
      H.candidateMatrix i j = S.accumulatedInverseCandidateEntry.entry i j
  candidateMatrixEntry_eq_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      H.candidateMatrix i j = generatedInteriorAccumulatedEntryValue T i j
  handoff_noLeftProductStatus :
    H.noLeftProductStatus = SM3db7RNoLeftProductStatus.noLeftProductInSM3db7RHandoff
  handoff_noRightProductStatus :
    H.noRightProductStatus = SM3db7RNoRightProductStatus.noRightProductInSM3db7RHandoff
  handoff_noTwoSidedInvStatus :
    H.noTwoSidedInvStatus = SM3db7RNoTwoSidedInvStatus.noTwoSidedInvInSM3db7RHandoff
  status_eq :
    status = SM3eRReRunHandoffShapeAuditStatus.handoffShapeAuditedFromSM3db7R
  noSM3daRFallbackStatus_eq :
    noSM3daRFallbackStatus = SM3eRReRunNoSM3daRFallbackStatus.noSM3daRFallbackInSM3eRReRun
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun

namespace GeneratedInteriorSM3db7RHandoffShapeAudit

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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

def fromHandoff
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInteriorSM3db7RHandoffShapeAudit Cell p A P wp W E K T M S H where
  status := SM3eRReRunHandoffShapeAuditStatus.handoffShapeAuditedFromSM3db7R
  mayConsumeOnlyHandoff := sm3eRMayConsumeOnlySM3dbRInverseCandidate_for_handoff H
  noSM3daRFallbackStatus := SM3eRReRunNoSM3daRFallbackStatus.noSM3daRFallbackInSM3eRReRun
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus := SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus :=
    SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  candidateMatrix_eq_SM3db6R_shapeSeparationMatrix :=
    handoffCandidate_eq_SM3db6R_shapeSeparationMatrix H
  candidateMatrixEntry_eq_SM3db5R_matrixExport := by
    intro i j
    exact handoffCandidate_source_eq_SM3db5R_matrixExport H i j
  candidateMatrixEntry_eq_SM3db4aR_accumulatedEntry := by
    intro i j
    exact handoffCandidate_source_eq_SM3db4aR_accumulatedEntry H i j
  candidateMatrixEntry_eq_accumulatedTraceValue := by
    intro i j
    exact H.candidateMatrixEntry_eq_accumulatedTraceValue i j
  handoff_noLeftProductStatus := noLeftProduct_for_SM3db7R H
  handoff_noRightProductStatus := noRightProduct_for_SM3db7R H
  handoff_noTwoSidedInvStatus := noTwoSidedInv_for_SM3db7R H
  status_eq := by
    rfl
  noSM3daRFallbackStatus_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RHandoffShapeAudit

structure GeneratedInteriorSM3db7RLeftProductAudit
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  shapeAudit : GeneratedInteriorSM3db7RHandoffShapeAudit Cell p A P wp W E K T M S H
  status : SM3eRReRunLeftProductStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  entry_eq_matrixProduct :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i j =
        (generatedInteriorBlock W * H.candidateMatrix) i j
  status_eq :
    status = SM3eRReRunLeftProductStatus.leftProductFromInteriorBlockAndHandoffCandidate
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun

namespace GeneratedInteriorSM3db7RLeftProductAudit

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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

def fromHandoff
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInteriorSM3db7RLeftProductAudit Cell p A P wp W E K T M S H where
  shapeAudit := GeneratedInteriorSM3db7RHandoffShapeAudit.fromHandoff H
  status := SM3eRReRunLeftProductStatus.leftProductFromInteriorBlockAndHandoffCandidate
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  entry_eq_matrixProduct := by
    intro i j
    exact generatedInteriorSM3db7RLeftProductEntry_eq_matrixProduct H i j
  status_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RLeftProductAudit

structure GeneratedInteriorSM3db7RRightProductAudit
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  shapeAudit : GeneratedInteriorSM3db7RHandoffShapeAudit Cell p A P wp W E K T M S H
  status : SM3eRReRunRightProductStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  entry_eq_matrixProduct :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i j =
        (H.candidateMatrix * generatedInteriorBlock W) i j
  status_eq :
    status = SM3eRReRunRightProductStatus.rightProductFromHandoffCandidateAndInteriorBlock
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun

namespace GeneratedInteriorSM3db7RRightProductAudit

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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

def fromHandoff
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInteriorSM3db7RRightProductAudit Cell p A P wp W E K T M S H where
  shapeAudit := GeneratedInteriorSM3db7RHandoffShapeAudit.fromHandoff H
  status := SM3eRReRunRightProductStatus.rightProductFromHandoffCandidateAndInteriorBlock
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  entry_eq_matrixProduct := by
    intro i j
    exact generatedInteriorSM3db7RRightProductEntry_eq_matrixProduct H i j
  status_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RRightProductAudit

def GeneratedInteriorSM3db7RLeftProductNormalForm
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ k : GeneratedInteriorIndex A,
    generatedInteriorBlock W i k * generatedInteriorAccumulatedEntryValue T k j

def GeneratedInteriorSM3db7RRightProductNormalForm
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ k : GeneratedInteriorIndex A,
    generatedInteriorAccumulatedEntryValue T i k * generatedInteriorBlock W k j

theorem leftProductEntry_expand_handoffCandidate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
      ∑ k : GeneratedInteriorIndex A,
        generatedInteriorBlock W i k * H.candidateMatrix k j := by
  calc
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
        (generatedInteriorBlock W * H.candidateMatrix) i j := by
          rfl
    _ = ∑ k : GeneratedInteriorIndex A,
          generatedInteriorBlock W i k * H.candidateMatrix k j := by
          rw [Matrix.mul_apply]

theorem rightProductEntry_expand_handoffCandidate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i j =
      ∑ k : GeneratedInteriorIndex A,
        H.candidateMatrix i k * generatedInteriorBlock W k j := by
  calc
    GeneratedInteriorSM3db7RRightProductEntry H i j =
        (H.candidateMatrix * generatedInteriorBlock W) i j := by
          rfl
    _ = ∑ k : GeneratedInteriorIndex A,
          H.candidateMatrix i k * generatedInteriorBlock W k j := by
          rw [Matrix.mul_apply]

theorem generatedInteriorSM3db7RLeftProductEntry_eq_sum_accumulated
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
      GeneratedInteriorSM3db7RLeftProductNormalForm T i j := by
  calc
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
        ∑ k : GeneratedInteriorIndex A,
          generatedInteriorBlock W i k * H.candidateMatrix k j :=
          leftProductEntry_expand_handoffCandidate H i j
    _ = ∑ k : GeneratedInteriorIndex A,
          generatedInteriorBlock W i k * generatedInteriorAccumulatedEntryValue T k j := by
          refine Finset.sum_congr rfl ?_
          intro k _
          exact congrArg
            (fun x : ℝ => generatedInteriorBlock W i k * x)
            (H.candidateMatrixEntry_eq_accumulatedTraceValue k j)

theorem generatedInteriorSM3db7RRightProductEntry_eq_sum_accumulated
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i j =
      GeneratedInteriorSM3db7RRightProductNormalForm T i j := by
  calc
    GeneratedInteriorSM3db7RRightProductEntry H i j =
        ∑ k : GeneratedInteriorIndex A,
          H.candidateMatrix i k * generatedInteriorBlock W k j :=
          rightProductEntry_expand_handoffCandidate H i j
    _ = ∑ k : GeneratedInteriorIndex A,
          generatedInteriorAccumulatedEntryValue T i k * generatedInteriorBlock W k j := by
          refine Finset.sum_congr rfl ?_
          intro k _
          exact congrArg
            (fun x : ℝ => x * generatedInteriorBlock W k j)
            (H.candidateMatrixEntry_eq_accumulatedTraceValue i k)

structure GeneratedInteriorSM3db7RProductNormalFormLedger
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  leftProductAudit : GeneratedInteriorSM3db7RLeftProductAudit Cell p A P wp W E K T M S H
  rightProductAudit : GeneratedInteriorSM3db7RRightProductAudit Cell p A P wp W E K T M S H
  status : SM3eRReRunProductNormalFormStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  noMatrixInvStatus : SM3eRReRunNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3eRReRunNoExternalInverseOracleStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  leftProduct_expand_handoffCandidate :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i j =
        ∑ k : GeneratedInteriorIndex A,
          generatedInteriorBlock W i k * H.candidateMatrix k j
  rightProduct_expand_handoffCandidate :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i j =
        ∑ k : GeneratedInteriorIndex A,
          H.candidateMatrix i k * generatedInteriorBlock W k j
  leftProductEntry_eq_sum_accumulated :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i j =
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j
  rightProductEntry_eq_sum_accumulated :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i j =
        GeneratedInteriorSM3db7RRightProductNormalForm T i j
  candidateMatrixEntry_eq_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      H.candidateMatrix i j = generatedInteriorAccumulatedEntryValue T i j
  status_eq :
    status =
      SM3eRReRunProductNormalFormStatus.productNormalFormsFromSM3db7RHandoffAccumulatedEntry
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun

namespace GeneratedInteriorSM3db7RProductNormalFormLedger

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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

def fromHandoff
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInteriorSM3db7RProductNormalFormLedger Cell p A P wp W E K T M S H where
  leftProductAudit := GeneratedInteriorSM3db7RLeftProductAudit.fromHandoff H
  rightProductAudit := GeneratedInteriorSM3db7RRightProductAudit.fromHandoff H
  status :=
    SM3eRReRunProductNormalFormStatus.productNormalFormsFromSM3db7RHandoffAccumulatedEntry
  noFreeEntryTableStatus := SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus := SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus :=
    SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  leftProduct_expand_handoffCandidate := by
    intro i j
    exact leftProductEntry_expand_handoffCandidate H i j
  rightProduct_expand_handoffCandidate := by
    intro i j
    exact rightProductEntry_expand_handoffCandidate H i j
  leftProductEntry_eq_sum_accumulated := by
    intro i j
    exact generatedInteriorSM3db7RLeftProductEntry_eq_sum_accumulated H i j
  rightProductEntry_eq_sum_accumulated := by
    intro i j
    exact generatedInteriorSM3db7RRightProductEntry_eq_sum_accumulated H i j
  candidateMatrixEntry_eq_accumulatedTraceValue := by
    intro i j
    exact H.candidateMatrixEntry_eq_accumulatedTraceValue i j
  status_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RProductNormalFormLedger


structure GeneratedInteriorSM3db7RTraceCancellationInvariant
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  productNormalFormLedger :
    GeneratedInteriorSM3db7RProductNormalFormLedger Cell p A P wp W E K T M S H
  status : SM3eRReRunTraceCancellationStatus
  noFreeEntryTableStatus : SM3eRReRunNoFreeEntryTableStatus
  noMatrixInvStatus : SM3eRReRunNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3eRReRunNoExternalInverseOracleStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedSourceStatus_eq_SM3db4aR :
    H.sourceAccumulatedEntry.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  productNormalFormStatus_eq :
    productNormalFormLedger.status =
      SM3eRReRunProductNormalFormStatus.productNormalFormsFromSM3db7RHandoffAccumulatedEntry
  leftNormalForm_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductNormalForm T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightNormalForm_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductNormalForm T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftNormalForm_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductNormalForm T i i = 1
  leftNormalForm_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RLeftProductNormalForm T i j = 0
  rightNormalForm_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductNormalForm T i i = 1
  rightNormalForm_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RRightProductNormalForm T i j = 0
  status_eq :
    status =
      SM3eRReRunTraceCancellationStatus.traceCancellationFromSM3db4aRAccumulatedEntryAndR3aNormalForms
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3eRReRunNoFreeEntryTableStatus.noFreeEntryTableInSM3eRReRun
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3eRReRunNoMatrixInvStatus.noMatrixInvInSM3eRReRun
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3eRReRunNoExternalInverseOracleStatus.noExternalInverseOracleInSM3eRReRun
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun

namespace GeneratedInteriorSM3db7RTraceCancellationInvariant

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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


theorem leftProduct_entry_eq_identity
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j := by
  calc
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j :=
          C.productNormalFormLedger.leftProductEntry_eq_sum_accumulated i j
    _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
          C.leftNormalForm_entry_eq_identity i j

theorem rightProduct_entry_eq_identity
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j := by
  calc
    GeneratedInteriorSM3db7RRightProductEntry H i j =
        GeneratedInteriorSM3db7RRightProductNormalForm T i j :=
          C.productNormalFormLedger.rightProductEntry_eq_sum_accumulated i j
    _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
          C.rightNormalForm_entry_eq_identity i j

theorem leftProduct_diagonal_entry
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i i = 1 := by
  calc
    GeneratedInteriorSM3db7RLeftProductEntry H i i =
        GeneratedInteriorSM3db7RLeftProductNormalForm T i i :=
          C.productNormalFormLedger.leftProductEntry_eq_sum_accumulated i i
    _ = 1 := C.leftNormalForm_diagonal_entry i

theorem leftProduct_offdiag_entry
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j = 0 := by
  calc
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j :=
          C.productNormalFormLedger.leftProductEntry_eq_sum_accumulated i j
    _ = 0 := C.leftNormalForm_offdiag_entry i j hij

theorem rightProduct_diagonal_entry
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i i = 1 := by
  calc
    GeneratedInteriorSM3db7RRightProductEntry H i i =
        GeneratedInteriorSM3db7RRightProductNormalForm T i i :=
          C.productNormalFormLedger.rightProductEntry_eq_sum_accumulated i i
    _ = 1 := C.rightNormalForm_diagonal_entry i

theorem rightProduct_offdiag_entry
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    GeneratedInteriorSM3db7RRightProductEntry H i j = 0 := by
  calc
    GeneratedInteriorSM3db7RRightProductEntry H i j =
        GeneratedInteriorSM3db7RRightProductNormalForm T i j :=
          C.productNormalFormLedger.rightProductEntry_eq_sum_accumulated i j
    _ = 0 := C.rightNormalForm_offdiag_entry i j hij

end GeneratedInteriorSM3db7RTraceCancellationInvariant

structure GeneratedInteriorSM3db7RProductCancellationLedger
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  productNormalFormLedger :
    GeneratedInteriorSM3db7RProductNormalFormLedger Cell p A P wp W E K T M S H
  traceCancellationInvariant :
    GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H
  status : SM3eRReRunProductCancellationLedgerStatus
  r4GateStatus : SM3eRReRunR4GateStatus
  noProductIdentityProofStatus : SM3eRReRunNoProductIdentityProofStatus
  sm3fGateStatus : SM3eRReRunSM3fGateStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRReRunNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRReRunNoArithmeticTargetStatus
  leftProduct_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightProduct_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftProduct_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i i = 1
  leftProduct_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RLeftProductEntry H i j = 0
  rightProduct_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i i = 1
  rightProduct_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RRightProductEntry H i j = 0
  status_eq :
    status =
      SM3eRReRunProductCancellationLedgerStatus.productCancellationLedgerFromTraceCancellation
  r4GateStatus_eq :
    r4GateStatus = SM3eRReRunR4GateStatus.r4ReadyAfterR3bCancellationFields
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus_eq :
    sm3fGateStatus = SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun

namespace GeneratedInteriorSM3db7RProductCancellationLedger

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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


def fromTraceCancellationInvariant
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H) :
    GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H where
  productNormalFormLedger := C.productNormalFormLedger
  traceCancellationInvariant := C
  status :=
    SM3eRReRunProductCancellationLedgerStatus.productCancellationLedgerFromTraceCancellation
  r4GateStatus := SM3eRReRunR4GateStatus.r4ReadyAfterR3bCancellationFields
  noProductIdentityProofStatus :=
    SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus := SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus := SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus :=
    SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun
  leftProduct_entry_eq_identity := by
    intro i j
    exact GeneratedInteriorSM3db7RTraceCancellationInvariant.leftProduct_entry_eq_identity C i j
  rightProduct_entry_eq_identity := by
    intro i j
    exact GeneratedInteriorSM3db7RTraceCancellationInvariant.rightProduct_entry_eq_identity C i j
  leftProduct_diagonal_entry := by
    intro i
    exact GeneratedInteriorSM3db7RTraceCancellationInvariant.leftProduct_diagonal_entry C i
  leftProduct_offdiag_entry := by
    intro i j hij
    exact GeneratedInteriorSM3db7RTraceCancellationInvariant.leftProduct_offdiag_entry C i j hij
  rightProduct_diagonal_entry := by
    intro i
    exact GeneratedInteriorSM3db7RTraceCancellationInvariant.rightProduct_diagonal_entry C i
  rightProduct_offdiag_entry := by
    intro i j hij
    exact GeneratedInteriorSM3db7RTraceCancellationInvariant.rightProduct_offdiag_entry C i j hij
  status_eq := by
    rfl
  r4GateStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  sm3fGateStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

theorem leftProduct_entry_eq_identity_of_ledger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  L.leftProduct_entry_eq_identity i j

theorem rightProduct_entry_eq_identity_of_ledger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  L.rightProduct_entry_eq_identity i j

theorem leftProduct_diagonal_entry_of_ledger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RLeftProductEntry H i i = 1 :=
  L.leftProduct_diagonal_entry i

theorem leftProduct_offdiag_entry_of_ledger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    GeneratedInteriorSM3db7RLeftProductEntry H i j = 0 :=
  L.leftProduct_offdiag_entry i j hij

theorem rightProduct_diagonal_entry_of_ledger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorSM3db7RRightProductEntry H i i = 1 :=
  L.rightProduct_diagonal_entry i

theorem rightProduct_offdiag_entry_of_ledger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    GeneratedInteriorSM3db7RRightProductEntry H i j = 0 :=
  L.rightProduct_offdiag_entry i j hij

end GeneratedInteriorSM3db7RProductCancellationLedger

structure GeneratedInteriorSM3db7RProductIdentityProof
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) : Prop where
  leftProduct_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightProduct_entry_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftProduct_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RLeftProductEntry H i i = 1
  leftProduct_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RLeftProductEntry H i j = 0
  rightProduct_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorSM3db7RRightProductEntry H i i = 1
  rightProduct_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorSM3db7RRightProductEntry H i j = 0

theorem generatedInteriorSM3db7RLeftProduct_matrix_eq_identity
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (Q : GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H) :
    generatedInteriorBlock W * H.candidateMatrix =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) := by
  funext i j
  change GeneratedInteriorSM3db7RLeftProductEntry H i j =
    (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  exact Q.leftProduct_entry_eq_identity i j

theorem generatedInteriorSM3db7RRightProduct_matrix_eq_identity
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (Q : GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H) :
    H.candidateMatrix * generatedInteriorBlock W =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) := by
  funext i j
  change GeneratedInteriorSM3db7RRightProductEntry H i j =
    (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  exact Q.rightProduct_entry_eq_identity i j

def provenTwoSidedInvFromSM3db7R
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
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
    (Q : GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H) :
    TwoSidedInv (generatedInteriorBlock W) H.candidateMatrix where
  left_inv := generatedInteriorSM3db7RLeftProduct_matrix_eq_identity Q
  right_inv := generatedInteriorSM3db7RRightProduct_matrix_eq_identity Q

structure GeneratedInteriorSM3db7RProductProofGate
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
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
  leftProductAudit : GeneratedInteriorSM3db7RLeftProductAudit Cell p A P wp W E K T M S H
  rightProductAudit : GeneratedInteriorSM3db7RRightProductAudit Cell p A P wp W E K T M S H
  diagonalOffdiagStatus : SM3eRReRunDiagonalOffdiagStatus
  proofGateStatus : SM3eRReRunProofGateStatus
  sm3fGateStatus : SM3eRReRunSM3fGateStatus
  noCertificateStatus : SM3eRReRunNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3eRReRunNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3eRReRunNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRReRunNoArithmeticTargetStatus
  diagonalOffdiagStatus_eq :
    diagonalOffdiagStatus = SM3eRReRunDiagonalOffdiagStatus.diagonalOffdiagGoalsProofCarrying
  proofGateStatus_eq :
    proofGateStatus = SM3eRReRunProofGateStatus.waitingForLeftAndRightProductIdentityProofs
  sm3fGateStatus_eq :
    sm3fGateStatus = SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun

namespace GeneratedInteriorSM3db7RProductProofGate

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
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

def fromHandoff
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInteriorSM3db7RProductProofGate Cell p A P wp W E K T M S H where
  leftProductAudit := GeneratedInteriorSM3db7RLeftProductAudit.fromHandoff H
  rightProductAudit := GeneratedInteriorSM3db7RRightProductAudit.fromHandoff H
  diagonalOffdiagStatus := SM3eRReRunDiagonalOffdiagStatus.diagonalOffdiagGoalsProofCarrying
  proofGateStatus := SM3eRReRunProofGateStatus.waitingForLeftAndRightProductIdentityProofs
  sm3fGateStatus := SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  noCertificateStatus :=
    SM3eRReRunNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eRReRun
  noInteriorEliminationDataStatus :=
    SM3eRReRunNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3eRReRun
  noDtnDataStatus := SM3eRReRunNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eRReRun
  noArithmeticTargetStatus :=
    SM3eRReRunNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eRReRun
  diagonalOffdiagStatus_eq := by
    rfl
  proofGateStatus_eq := by
    rfl
  sm3fGateStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

end GeneratedInteriorSM3db7RProductProofGate

def regularGeneratedInteriorSM3db7RHandoffShapeAudit
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RHandoffShapeAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RHandoffShapeAudit.fromHandoff
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableGeneratedInteriorSM3db7RHandoffShapeAudit
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RHandoffShapeAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RHandoffShapeAudit.fromHandoff
    (variableSM3dbRToSM3eRHandoff β p wp)

def regularGeneratedInteriorSM3db7RLeftProductAudit
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RLeftProductAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RLeftProductAudit.fromHandoff
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableGeneratedInteriorSM3db7RLeftProductAudit
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RLeftProductAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RLeftProductAudit.fromHandoff
    (variableSM3dbRToSM3eRHandoff β p wp)

def regularGeneratedInteriorSM3db7RRightProductAudit
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RRightProductAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RRightProductAudit.fromHandoff
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableGeneratedInteriorSM3db7RRightProductAudit
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RRightProductAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RRightProductAudit.fromHandoff
    (variableSM3dbRToSM3eRHandoff β p wp)

def regularGeneratedInteriorSM3db7RProductNormalFormLedger
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RProductNormalFormLedger
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RProductNormalFormLedger.fromHandoff
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableGeneratedInteriorSM3db7RProductNormalFormLedger
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RProductNormalFormLedger
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RProductNormalFormLedger.fromHandoff
    (variableSM3dbRToSM3eRHandoff β p wp)


def regularGeneratedInteriorSM3db7RProductCancellationLedger
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp)) :
    GeneratedInteriorSM3db7RProductCancellationLedger
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RProductCancellationLedger.fromTraceCancellationInvariant C

def variableGeneratedInteriorSM3db7RProductCancellationLedger
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp)) :
    GeneratedInteriorSM3db7RProductCancellationLedger
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RProductCancellationLedger.fromTraceCancellationInvariant C

def regularGeneratedInteriorSM3db7RProductProofGate
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RProductProofGate
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInteriorSM3db7RProductProofGate.fromHandoff
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableGeneratedInteriorSM3db7RProductProofGate
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorSM3db7RProductProofGate
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInteriorSM3db7RProductProofGate.fromHandoff
    (variableSM3dbRToSM3eRHandoff β p wp)

structure SM3eRReRunGeneratedTwoSidedInvLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3eRReRunLedgerStatus
  regularShapeAudit :
    GeneratedInteriorSM3db7RHandoffShapeAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableShapeAudit :
    GeneratedInteriorSM3db7RHandoffShapeAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularLeftProductAudit :
    GeneratedInteriorSM3db7RLeftProductAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableLeftProductAudit :
    GeneratedInteriorSM3db7RLeftProductAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularRightProductAudit :
    GeneratedInteriorSM3db7RRightProductAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableRightProductAudit :
    GeneratedInteriorSM3db7RRightProductAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularProductProofGate :
    GeneratedInteriorSM3db7RProductProofGate
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableProductProofGate :
    GeneratedInteriorSM3db7RProductProofGate
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularCandidateFromSM3db7RHandoff :
    (regularSM3dbRToSM3eRHandoff b p regularWeight).candidateMatrix =
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight).matrix
  variableCandidateFromSM3db7RHandoff :
    (variableSM3dbRToSM3eRHandoff β p variableWeight).candidateMatrix =
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight).matrix
  regularLeftProductStatus_eq :
    regularLeftProductAudit.status =
      SM3eRReRunLeftProductStatus.leftProductFromInteriorBlockAndHandoffCandidate
  variableLeftProductStatus_eq :
    variableLeftProductAudit.status =
      SM3eRReRunLeftProductStatus.leftProductFromInteriorBlockAndHandoffCandidate
  regularRightProductStatus_eq :
    regularRightProductAudit.status =
      SM3eRReRunRightProductStatus.rightProductFromHandoffCandidateAndInteriorBlock
  variableRightProductStatus_eq :
    variableRightProductAudit.status =
      SM3eRReRunRightProductStatus.rightProductFromHandoffCandidateAndInteriorBlock
  regularProofGate_eq :
    regularProductProofGate.proofGateStatus =
      SM3eRReRunProofGateStatus.waitingForLeftAndRightProductIdentityProofs
  variableProofGate_eq :
    variableProductProofGate.proofGateStatus =
      SM3eRReRunProofGateStatus.waitingForLeftAndRightProductIdentityProofs
  regularSM3fGate_eq :
    regularProductProofGate.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  variableSM3fGate_eq :
    variableProductProofGate.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  status_eq : status = SM3eRReRunLedgerStatus.handoffProductCalculusPrepared

def sm3eRReRunGeneratedTwoSidedInvLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3eRReRunGeneratedTwoSidedInvLedger b β p regularWeight variableWeight where
  status := SM3eRReRunLedgerStatus.handoffProductCalculusPrepared
  regularShapeAudit := regularGeneratedInteriorSM3db7RHandoffShapeAudit b p regularWeight
  variableShapeAudit := variableGeneratedInteriorSM3db7RHandoffShapeAudit β p variableWeight
  regularLeftProductAudit := regularGeneratedInteriorSM3db7RLeftProductAudit b p regularWeight
  variableLeftProductAudit := variableGeneratedInteriorSM3db7RLeftProductAudit β p variableWeight
  regularRightProductAudit := regularGeneratedInteriorSM3db7RRightProductAudit b p regularWeight
  variableRightProductAudit := variableGeneratedInteriorSM3db7RRightProductAudit β p variableWeight
  regularProductProofGate := regularGeneratedInteriorSM3db7RProductProofGate b p regularWeight
  variableProductProofGate := variableGeneratedInteriorSM3db7RProductProofGate β p variableWeight
  regularCandidateFromSM3db7RHandoff :=
    handoffCandidate_eq_SM3db6R_shapeSeparationMatrix
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableCandidateFromSM3db7RHandoff :=
    handoffCandidate_eq_SM3db6R_shapeSeparationMatrix
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularLeftProductStatus_eq := by
    rfl
  variableLeftProductStatus_eq := by
    rfl
  regularRightProductStatus_eq := by
    rfl
  variableRightProductStatus_eq := by
    rfl
  regularProofGate_eq := by
    rfl
  variableProofGate_eq := by
    rfl
  regularSM3fGate_eq := by
    rfl
  variableSM3fGate_eq := by
    rfl
  status_eq := by
    rfl

theorem sm3eRReRunGeneratedTwoSidedInvLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRReRunGeneratedTwoSidedInvLedger b β p regularWeight variableWeight).status =
      SM3eRReRunLedgerStatus.handoffProductCalculusPrepared := by
  rfl

theorem sm3eRReRunGeneratedTwoSidedInvLedger_regularProofGate
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRReRunGeneratedTwoSidedInvLedger
      b β p regularWeight variableWeight).regularProductProofGate.proofGateStatus =
      SM3eRReRunProofGateStatus.waitingForLeftAndRightProductIdentityProofs := by
  rfl

theorem sm3eRReRunGeneratedTwoSidedInvLedger_variableSM3fBlocked
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRReRunGeneratedTwoSidedInvLedger
      b β p regularWeight variableWeight).variableProductProofGate.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv := by
  rfl

structure SM3eRReRunGeneratedProductNormalFormLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularProductNormalFormLedger :
    GeneratedInteriorSM3db7RProductNormalFormLedger
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableProductNormalFormLedger :
    GeneratedInteriorSM3db7RProductNormalFormLedger
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularStatus_eq :
    regularProductNormalFormLedger.status =
      SM3eRReRunProductNormalFormStatus.productNormalFormsFromSM3db7RHandoffAccumulatedEntry
  variableStatus_eq :
    variableProductNormalFormLedger.status =
      SM3eRReRunProductNormalFormStatus.productNormalFormsFromSM3db7RHandoffAccumulatedEntry
  regularSM3fStillBlocked :
    (regularGeneratedInteriorSM3db7RProductProofGate b p regularWeight).sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  variableSM3fStillBlocked :
    (variableGeneratedInteriorSM3db7RProductProofGate β p variableWeight).sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv

def sm3eRReRunGeneratedProductNormalFormLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3eRReRunGeneratedProductNormalFormLedger b β p regularWeight variableWeight where
  regularProductNormalFormLedger :=
    regularGeneratedInteriorSM3db7RProductNormalFormLedger b p regularWeight
  variableProductNormalFormLedger :=
    variableGeneratedInteriorSM3db7RProductNormalFormLedger β p variableWeight
  regularStatus_eq := by
    rfl
  variableStatus_eq := by
    rfl
  regularSM3fStillBlocked := by
    rfl
  variableSM3fStillBlocked := by
    rfl

theorem sm3eRReRunGeneratedProductNormalFormLedger_regularStatus
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRReRunGeneratedProductNormalFormLedger
      b β p regularWeight variableWeight).regularProductNormalFormLedger.status =
      SM3eRReRunProductNormalFormStatus.productNormalFormsFromSM3db7RHandoffAccumulatedEntry := by
  rfl

theorem sm3eRReRunGeneratedProductNormalFormLedger_variableSM3fBlocked
    (β : Nat → Nat) (p : ConcretePolicyOf) (variableWeight : WeightPolicy) :
    (variableGeneratedInteriorSM3db7RProductProofGate β p variableWeight).sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv := by
  rfl


structure SM3eRReRunGeneratedProductCancellationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularProductCancellationLedger :
    GeneratedInteriorSM3db7RProductCancellationLedger
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableProductCancellationLedger :
    GeneratedInteriorSM3db7RProductCancellationLedger
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  regularStatus_eq :
    regularProductCancellationLedger.status =
      SM3eRReRunProductCancellationLedgerStatus.productCancellationLedgerFromTraceCancellation
  variableStatus_eq :
    variableProductCancellationLedger.status =
      SM3eRReRunProductCancellationLedgerStatus.productCancellationLedgerFromTraceCancellation
  regularR4Gate_eq :
    regularProductCancellationLedger.r4GateStatus =
      SM3eRReRunR4GateStatus.r4ReadyAfterR3bCancellationFields
  variableR4Gate_eq :
    variableProductCancellationLedger.r4GateStatus =
      SM3eRReRunR4GateStatus.r4ReadyAfterR3bCancellationFields
  regularNoProductIdentityProof_eq :
    regularProductCancellationLedger.noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  variableNoProductIdentityProof_eq :
    variableProductCancellationLedger.noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  regularSM3fStillBlocked :
    regularProductCancellationLedger.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  variableSM3fStillBlocked :
    variableProductCancellationLedger.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv

def sm3eRReRunGeneratedProductCancellationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularCancellation : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight))
    (variableCancellation : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)) :
    SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight where
  regularProductCancellationLedger :=
    regularGeneratedInteriorSM3db7RProductCancellationLedger
      b p regularWeight regularCancellation
  variableProductCancellationLedger :=
    variableGeneratedInteriorSM3db7RProductCancellationLedger
      β p variableWeight variableCancellation
  regularStatus_eq := by
    rfl
  variableStatus_eq := by
    rfl
  regularR4Gate_eq := by
    rfl
  variableR4Gate_eq := by
    rfl
  regularNoProductIdentityProof_eq := by
    rfl
  variableNoProductIdentityProof_eq := by
    rfl
  regularSM3fStillBlocked := by
    rfl
  variableSM3fStillBlocked := by
    rfl

theorem sm3eRReRunGeneratedProductCancellationLedger_regularR4Gate
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularCancellation : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight))
    (variableCancellation : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)) :
    (sm3eRReRunGeneratedProductCancellationLedger
      b β p regularWeight variableWeight regularCancellation variableCancellation).regularProductCancellationLedger.r4GateStatus =
      SM3eRReRunR4GateStatus.r4ReadyAfterR3bCancellationFields := by
  rfl

theorem sm3eRReRunGeneratedProductCancellationLedger_variableSM3fBlocked
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularCancellation : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight))
    (variableCancellation : GeneratedInteriorSM3db7RTraceCancellationInvariant
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)) :
    (sm3eRReRunGeneratedProductCancellationLedger
      b β p regularWeight variableWeight regularCancellation variableCancellation).variableProductCancellationLedger.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
