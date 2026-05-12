import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db6RShapeSeparationStatus where
  | shapeSeparationFromSM3db5RMatrix
  deriving DecidableEq, Repr

inductive SM3db6RSourceSeparationStatus where
  | sourceSeparatedAsSM3db4aRAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3db6RNoSM3daRCandidateEntryFallbackStatus where
  | noSM3daRCandidateEntryFallback
  deriving DecidableEq, Repr

inductive SM3db6RNoInteriorBlockFallbackStatus where
  | noInteriorBlockFallbackWithoutFutureInvolutiveProof
  deriving DecidableEq, Repr

inductive SM3db6RInvolutiveBlockProofGateStatus where
  | involutiveBlockProofDeferredToSM3eRProductPhase
  deriving DecidableEq, Repr

inductive SM3db6RNoLocalResidualWrapperFallbackStatus where
  | noOnlyLocalResidualWrapperFallback
  deriving DecidableEq, Repr

inductive SM3db6RNoFreeTableStatus where
  | noFreeMatrixOrEntryTableInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoMatrixInvStatus where
  | noMatrixInvInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoProductProofStatus where
  | noProductProofInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoTwoSidedInvStatus where
  | noTwoSidedInvInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInShapeSeparation
  deriving DecidableEq, Repr

inductive SM3db6RNextGateStatus where
  | sm3db7RHandoffAfterShapeSeparation
  deriving DecidableEq, Repr

inductive SM3dbRShapeSeparationLedgerStatus where
  | shapeSeparationClosedAfterPositiveMatrixExport
  deriving DecidableEq, Repr

structure GeneratedInteriorInverseCandidateShapeSeparation
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
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T) where
  sourceMatrix : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T
  sourceCandidateEntry : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W
  accumulatedInverseCandidateEntry :
    GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T
  matrix : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ
  shapeSeparationStatus : SM3db6RShapeSeparationStatus
  sourceSeparationStatus : SM3db6RSourceSeparationStatus
  noSM3daRCandidateEntryFallbackStatus :
    SM3db6RNoSM3daRCandidateEntryFallbackStatus
  noInteriorBlockFallbackStatus : SM3db6RNoInteriorBlockFallbackStatus
  involutiveBlockProofGateStatus : SM3db6RInvolutiveBlockProofGateStatus
  noLocalResidualWrapperFallbackStatus : SM3db6RNoLocalResidualWrapperFallbackStatus
  notOnlyLocalResidualWrapperStatus : SM3db4aRNotOnlyLocalResidualWrapperStatus
  noFreeTableStatus : SM3db6RNoFreeTableStatus
  noMatrixInvStatus : SM3db6RNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noProductProofStatus : SM3db6RNoProductProofStatus
  noTwoSidedInvStatus : SM3db6RNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus :
    SM3db6RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db6RNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db6RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db6RNoArithmeticTargetStatus
  nextGateStatus : SM3db6RNextGateStatus
  sourceMatrix_eq : sourceMatrix = M
  sourceCandidateEntry_eq : sourceCandidateEntry = M.sourceCandidateEntry
  accumulatedInverseCandidateEntry_eq :
    accumulatedInverseCandidateEntry = M.accumulatedInverseCandidateEntry
  matrix_eq : matrix = M.matrix
  matrixEntry_from_SM3db5RMatrix :
    ∀ i j : GeneratedInteriorIndex A,
      matrix i j = M.matrix i j
  matrixEntry_from_accumulatedEntry :
    ∀ i j : GeneratedInteriorIndex A,
      matrix i j = accumulatedInverseCandidateEntry.entry i j
  matrixEntry_from_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      matrix i j = generatedInteriorAccumulatedEntryValue T i j
  sourceMatrix_from_accumulatedEntry :
    M.matrix = inverseCandidateMatrix_from_accumulatedEntry M.accumulatedInverseCandidateEntry
  sourceStatus_eq_SM3db5R :
    M.sourceStatus =
      SM3db5RInverseCandidateMatrixSourceStatus.matrixEntriesFromSM3db4aRAccumulatedEntry
  accumulatedSourceStatus_eq_SM3db4aR :
    accumulatedInverseCandidateEntry.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedEntry_notOnlyLocalResidualWrapper :
    accumulatedInverseCandidateEntry.notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  shapeSeparationStatus_eq :
    shapeSeparationStatus = SM3db6RShapeSeparationStatus.shapeSeparationFromSM3db5RMatrix
  sourceSeparationStatus_eq :
    sourceSeparationStatus =
      SM3db6RSourceSeparationStatus.sourceSeparatedAsSM3db4aRAccumulatedEntry
  noSM3daRCandidateEntryFallbackStatus_eq :
    noSM3daRCandidateEntryFallbackStatus =
      SM3db6RNoSM3daRCandidateEntryFallbackStatus.noSM3daRCandidateEntryFallback
  noInteriorBlockFallbackStatus_eq :
    noInteriorBlockFallbackStatus =
      SM3db6RNoInteriorBlockFallbackStatus.noInteriorBlockFallbackWithoutFutureInvolutiveProof
  involutiveBlockProofGateStatus_eq :
    involutiveBlockProofGateStatus =
      SM3db6RInvolutiveBlockProofGateStatus.involutiveBlockProofDeferredToSM3eRProductPhase
  noLocalResidualWrapperFallbackStatus_eq :
    noLocalResidualWrapperFallbackStatus =
      SM3db6RNoLocalResidualWrapperFallbackStatus.noOnlyLocalResidualWrapperFallback
  notOnlyLocalResidualWrapperStatus_eq :
    notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  noFreeTableStatus_eq :
    noFreeTableStatus = SM3db6RNoFreeTableStatus.noFreeMatrixOrEntryTableInShapeSeparation
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db6RNoMatrixInvStatus.noMatrixInvInShapeSeparation
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noProductProofStatus_eq :
    noProductProofStatus = SM3db6RNoProductProofStatus.noProductProofInShapeSeparation
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db6RNoTwoSidedInvStatus.noTwoSidedInvInShapeSeparation
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3db6RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInShapeSeparation
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db6RNoInteriorEliminationDataStatus.noInteriorEliminationDataInShapeSeparation
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db6RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInShapeSeparation
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db6RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInShapeSeparation
  nextGateStatus_eq :
    nextGateStatus = SM3db6RNextGateStatus.sm3db7RHandoffAfterShapeSeparation

namespace GeneratedInteriorInverseCandidateShapeSeparation

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

def fromSM3db5RMatrix
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T) :
    GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M where
  sourceMatrix := M
  sourceCandidateEntry := M.sourceCandidateEntry
  accumulatedInverseCandidateEntry := M.accumulatedInverseCandidateEntry
  matrix := M.matrix
  shapeSeparationStatus := SM3db6RShapeSeparationStatus.shapeSeparationFromSM3db5RMatrix
  sourceSeparationStatus :=
    SM3db6RSourceSeparationStatus.sourceSeparatedAsSM3db4aRAccumulatedEntry
  noSM3daRCandidateEntryFallbackStatus :=
    SM3db6RNoSM3daRCandidateEntryFallbackStatus.noSM3daRCandidateEntryFallback
  noInteriorBlockFallbackStatus :=
    SM3db6RNoInteriorBlockFallbackStatus.noInteriorBlockFallbackWithoutFutureInvolutiveProof
  involutiveBlockProofGateStatus :=
    SM3db6RInvolutiveBlockProofGateStatus.involutiveBlockProofDeferredToSM3eRProductPhase
  noLocalResidualWrapperFallbackStatus :=
    SM3db6RNoLocalResidualWrapperFallbackStatus.noOnlyLocalResidualWrapperFallback
  notOnlyLocalResidualWrapperStatus :=
    M.accumulatedInverseCandidateEntry.notOnlyLocalResidualWrapperStatus
  noFreeTableStatus := SM3db6RNoFreeTableStatus.noFreeMatrixOrEntryTableInShapeSeparation
  noMatrixInvStatus := SM3db6RNoMatrixInvStatus.noMatrixInvInShapeSeparation
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noProductProofStatus := SM3db6RNoProductProofStatus.noProductProofInShapeSeparation
  noTwoSidedInvStatus := SM3db6RNoTwoSidedInvStatus.noTwoSidedInvInShapeSeparation
  noInteriorEliminationCertificateStatus :=
    SM3db6RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInShapeSeparation
  noInteriorEliminationDataStatus :=
    SM3db6RNoInteriorEliminationDataStatus.noInteriorEliminationDataInShapeSeparation
  noDtnDataStatus :=
    SM3db6RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInShapeSeparation
  noArithmeticTargetStatus :=
    SM3db6RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInShapeSeparation
  nextGateStatus := SM3db6RNextGateStatus.sm3db7RHandoffAfterShapeSeparation
  sourceMatrix_eq := by
    rfl
  sourceCandidateEntry_eq := by
    rfl
  accumulatedInverseCandidateEntry_eq := by
    rfl
  matrix_eq := by
    rfl
  matrixEntry_from_SM3db5RMatrix := by
    intro i j
    rfl
  matrixEntry_from_accumulatedEntry := by
    intro i j
    exact M.matrixEntry_from_accumulatedEntry i j
  matrixEntry_from_accumulatedTraceValue := by
    intro i j
    exact M.matrixEntry_from_accumulatedTraceValue i j
  sourceMatrix_from_accumulatedEntry :=
    M.matrix_from_accumulatedEntry
  sourceStatus_eq_SM3db5R :=
    M.sourceStatus_eq
  accumulatedSourceStatus_eq_SM3db4aR :=
    M.accumulatedInverseCandidateEntry.source_is_accumulatedTraceEvaluation
  accumulatedEntry_notOnlyLocalResidualWrapper :=
    M.accumulatedInverseCandidateEntry.notOnlyLocalResidualWrapperStatus_eq
  shapeSeparationStatus_eq := by
    rfl
  sourceSeparationStatus_eq := by
    rfl
  noSM3daRCandidateEntryFallbackStatus_eq := by
    rfl
  noInteriorBlockFallbackStatus_eq := by
    rfl
  involutiveBlockProofGateStatus_eq := by
    rfl
  noLocalResidualWrapperFallbackStatus_eq := by
    rfl
  notOnlyLocalResidualWrapperStatus_eq :=
    M.accumulatedInverseCandidateEntry.notOnlyLocalResidualWrapperStatus_eq
  noFreeTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noProductProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextGateStatus_eq := by
    rfl

end GeneratedInteriorInverseCandidateShapeSeparation

def inverseCandidateShapeSeparation_from_matrix
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
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T) :
    GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M :=
  GeneratedInteriorInverseCandidateShapeSeparation.fromSM3db5RMatrix M

theorem inverseCandidateEntry_not_SM3daR_candidateEntry
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    S.noSM3daRCandidateEntryFallbackStatus =
      SM3db6RNoSM3daRCandidateEntryFallbackStatus.noSM3daRCandidateEntryFallback :=
  S.noSM3daRCandidateEntryFallbackStatus_eq

theorem inverseCandidateEntry_not_interiorBlock_or_involutiveBlockProof
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    S.noInteriorBlockFallbackStatus =
      SM3db6RNoInteriorBlockFallbackStatus.noInteriorBlockFallbackWithoutFutureInvolutiveProof :=
  S.noInteriorBlockFallbackStatus_eq

theorem inverseCandidateMatrix_not_interiorBlock_or_involutiveBlockProof
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    S.involutiveBlockProofGateStatus =
      SM3db6RInvolutiveBlockProofGateStatus.involutiveBlockProofDeferredToSM3eRProductPhase :=
  S.involutiveBlockProofGateStatus_eq

theorem inverseCandidateMatrix_not_only_localResidualWrapper
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    S.notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper :=
  S.notOnlyLocalResidualWrapperStatus_eq

theorem inverseCandidateMatrix_entry_eq_accumulatedTraceValue_afterShapeSeparation
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (i j : GeneratedInteriorIndex A) :
    S.matrix i j = generatedInteriorAccumulatedEntryValue T i j :=
  S.matrixEntry_from_accumulatedTraceValue i j

theorem noProductProof_for_shapeSeparation
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    S.noProductProofStatus = SM3db6RNoProductProofStatus.noProductProofInShapeSeparation :=
  S.noProductProofStatus_eq

theorem noTwoSidedInv_for_shapeSeparation
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
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M) :
    S.noTwoSidedInvStatus = SM3db6RNoTwoSidedInvStatus.noTwoSidedInvInShapeSeparation :=
  S.noTwoSidedInvStatus_eq

def regularGeneratedInteriorInverseCandidateShapeSeparation
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorInverseCandidateShapeSeparation
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp) :=
  inverseCandidateShapeSeparation_from_matrix
    (regularGeneratedInteriorInverseCandidateMatrix b p wp)

def variableGeneratedInteriorInverseCandidateShapeSeparation
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorInverseCandidateShapeSeparation
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp) :=
  inverseCandidateShapeSeparation_from_matrix
    (variableGeneratedInteriorInverseCandidateMatrix β p wp)

structure SM3dbRShapeSeparationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3dbRShapeSeparationLedgerStatus
  sm3db5RLedger :
    SM3db5RGeneratedInteriorInverseCandidateMatrixLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularShapeSeparation :
    GeneratedInteriorInverseCandidateShapeSeparation
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
  variableShapeSeparation :
    GeneratedInteriorInverseCandidateShapeSeparation
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
  sm3db5RLedger_eq_main :
    sm3db5RLedger =
      sm3db5RGeneratedInteriorInverseCandidateMatrixLedger
        b β p regularWeight variableWeight regularPivot variablePivot
  regularMatrixEntryFromAccumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p),
      regularShapeSeparation.matrix i j =
        generatedInteriorAccumulatedEntryValue
          (regularGeneratedInteriorEliminationTrace b p regularWeight) i j
  variableMatrixEntryFromAccumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p),
      variableShapeSeparation.matrix i j =
        generatedInteriorAccumulatedEntryValue
          (variableGeneratedInteriorEliminationTrace β p variableWeight) i j
  regularNotSM3daRFallback :
    regularShapeSeparation.noSM3daRCandidateEntryFallbackStatus =
      SM3db6RNoSM3daRCandidateEntryFallbackStatus.noSM3daRCandidateEntryFallback
  variableNotSM3daRFallback :
    variableShapeSeparation.noSM3daRCandidateEntryFallbackStatus =
      SM3db6RNoSM3daRCandidateEntryFallbackStatus.noSM3daRCandidateEntryFallback
  regularNoInteriorBlockFallbackWithoutFutureInvolutiveProof :
    regularShapeSeparation.noInteriorBlockFallbackStatus =
      SM3db6RNoInteriorBlockFallbackStatus.noInteriorBlockFallbackWithoutFutureInvolutiveProof
  variableNoInteriorBlockFallbackWithoutFutureInvolutiveProof :
    variableShapeSeparation.noInteriorBlockFallbackStatus =
      SM3db6RNoInteriorBlockFallbackStatus.noInteriorBlockFallbackWithoutFutureInvolutiveProof
  regularNoOnlyLocalResidualWrapperFallback :
    regularShapeSeparation.notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  variableNoOnlyLocalResidualWrapperFallback :
    variableShapeSeparation.notOnlyLocalResidualWrapperStatus =
      SM3db4aRNotOnlyLocalResidualWrapperStatus.notOnlyLocalResidualWrapper
  regularNoProductProof :
    regularShapeSeparation.noProductProofStatus =
      SM3db6RNoProductProofStatus.noProductProofInShapeSeparation
  variableNoProductProof :
    variableShapeSeparation.noProductProofStatus =
      SM3db6RNoProductProofStatus.noProductProofInShapeSeparation
  regularNoTwoSidedInv :
    regularShapeSeparation.noTwoSidedInvStatus =
      SM3db6RNoTwoSidedInvStatus.noTwoSidedInvInShapeSeparation
  variableNoTwoSidedInv :
    variableShapeSeparation.noTwoSidedInvStatus =
      SM3db6RNoTwoSidedInvStatus.noTwoSidedInvInShapeSeparation
  regularNextGate :
    regularShapeSeparation.nextGateStatus =
      SM3db6RNextGateStatus.sm3db7RHandoffAfterShapeSeparation
  variableNextGate :
    variableShapeSeparation.nextGateStatus =
      SM3db6RNextGateStatus.sm3db7RHandoffAfterShapeSeparation
  status_eq_closed :
    status = SM3dbRShapeSeparationLedgerStatus.shapeSeparationClosedAfterPositiveMatrixExport

def sm3dbRShapeSeparationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3dbRShapeSeparationLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status := SM3dbRShapeSeparationLedgerStatus.shapeSeparationClosedAfterPositiveMatrixExport
  sm3db5RLedger :=
    sm3db5RGeneratedInteriorInverseCandidateMatrixLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularShapeSeparation :=
    regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight
  variableShapeSeparation :=
    variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight
  sm3db5RLedger_eq_main := by
    rfl
  regularMatrixEntryFromAccumulatedTraceValue := by
    intro i j
    exact
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight).matrixEntry_from_accumulatedTraceValue i j
  variableMatrixEntryFromAccumulatedTraceValue := by
    intro i j
    exact
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight).matrixEntry_from_accumulatedTraceValue i j
  regularNotSM3daRFallback :=
    (regularGeneratedInteriorInverseCandidateShapeSeparation
      b p regularWeight).noSM3daRCandidateEntryFallbackStatus_eq
  variableNotSM3daRFallback :=
    (variableGeneratedInteriorInverseCandidateShapeSeparation
      β p variableWeight).noSM3daRCandidateEntryFallbackStatus_eq
  regularNoInteriorBlockFallbackWithoutFutureInvolutiveProof :=
    (regularGeneratedInteriorInverseCandidateShapeSeparation
      b p regularWeight).noInteriorBlockFallbackStatus_eq
  variableNoInteriorBlockFallbackWithoutFutureInvolutiveProof :=
    (variableGeneratedInteriorInverseCandidateShapeSeparation
      β p variableWeight).noInteriorBlockFallbackStatus_eq
  regularNoOnlyLocalResidualWrapperFallback :=
    (regularGeneratedInteriorInverseCandidateShapeSeparation
      b p regularWeight).notOnlyLocalResidualWrapperStatus_eq
  variableNoOnlyLocalResidualWrapperFallback :=
    (variableGeneratedInteriorInverseCandidateShapeSeparation
      β p variableWeight).notOnlyLocalResidualWrapperStatus_eq
  regularNoProductProof :=
    (regularGeneratedInteriorInverseCandidateShapeSeparation
      b p regularWeight).noProductProofStatus_eq
  variableNoProductProof :=
    (variableGeneratedInteriorInverseCandidateShapeSeparation
      β p variableWeight).noProductProofStatus_eq
  regularNoTwoSidedInv :=
    (regularGeneratedInteriorInverseCandidateShapeSeparation
      b p regularWeight).noTwoSidedInvStatus_eq
  variableNoTwoSidedInv :=
    (variableGeneratedInteriorInverseCandidateShapeSeparation
      β p variableWeight).noTwoSidedInvStatus_eq
  regularNextGate :=
    (regularGeneratedInteriorInverseCandidateShapeSeparation
      b p regularWeight).nextGateStatus_eq
  variableNextGate :=
    (variableGeneratedInteriorInverseCandidateShapeSeparation
      β p variableWeight).nextGateStatus_eq
  status_eq_closed := by
    rfl

theorem sm3dbRShapeSeparationLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3dbRShapeSeparationLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3dbRShapeSeparationLedgerStatus.shapeSeparationClosedAfterPositiveMatrixExport := by
  rfl

theorem sm3dbRShapeSeparationLedger_regularNextGate
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3dbRShapeSeparationLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularShapeSeparation.nextGateStatus =
      SM3db6RNextGateStatus.sm3db7RHandoffAfterShapeSeparation := by
  rfl

theorem sm3dbRShapeSeparationLedger_regularNoProductProof
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3dbRShapeSeparationLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularShapeSeparation.noProductProofStatus =
      SM3db6RNoProductProofStatus.noProductProofInShapeSeparation := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
