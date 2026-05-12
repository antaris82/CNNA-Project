import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db5RInverseCandidateMatrixExportStatus where
  | inverseCandidateMatrixFromAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3db5RInverseCandidateMatrixSourceStatus where
  | matrixEntriesFromSM3db4aRAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3db5RNoFreeMatrixStatus where
  | noFreeMatrixOrEntryTable
  deriving DecidableEq, Repr

inductive SM3db5RNoMatrixInvStatus where
  | noMatrixInvInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNoSM3daRInteriorBlockFallbackStatus where
  | noSM3daRInteriorBlockFallback
  deriving DecidableEq, Repr

inductive SM3db5RNoProductProofStatus where
  | noProductProofInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db5R
  deriving DecidableEq, Repr

inductive SM3db5RNextGateStatus where
  | sm3db6RShapeSeparationAfterMatrixExport
  deriving DecidableEq, Repr

inductive SM3db5RGeneratedInteriorInverseCandidateMatrixLedgerStatus where
  | generatedInteriorInverseCandidateMatrixExportClosed
  deriving DecidableEq, Repr

def inverseCandidateMatrix_from_accumulatedEntry
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
    (I : GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ :=
  fun i j => I.entry i j

structure GeneratedInteriorInverseCandidateMatrix
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  sourceCandidateEntry : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W
  accumulatedInverseCandidateEntry :
    GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T
  matrix : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ
  exportStatus : SM3db5RInverseCandidateMatrixExportStatus
  sourceStatus : SM3db5RInverseCandidateMatrixSourceStatus
  noFreeMatrixStatus : SM3db5RNoFreeMatrixStatus
  noMatrixInvStatus : SM3db5RNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noSM3daRInteriorBlockFallbackStatus : SM3db5RNoSM3daRInteriorBlockFallbackStatus
  noProductProofStatus : SM3db5RNoProductProofStatus
  noTwoSidedInvStatus : SM3db5RNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus :
    SM3db5RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db5RNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db5RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db5RNoArithmeticTargetStatus
  nextGateStatus : SM3db5RNextGateStatus
  sourceCandidateEntry_is_source : sourceCandidateEntry = E
  accumulatedInverseCandidateEntry_is_fromTrace :
    accumulatedInverseCandidateEntry =
      GeneratedInteriorAccumulatedInverseCandidateEntry.fromAccumulatedTraceEvaluation T
  matrixEntry_from_accumulatedEntry :
    ∀ i j : GeneratedInteriorIndex A,
      matrix i j = accumulatedInverseCandidateEntry.entry i j
  matrixEntry_from_accumulatedTraceValue :
    ∀ i j : GeneratedInteriorIndex A,
      matrix i j = generatedInteriorAccumulatedEntryValue T i j
  matrix_from_accumulatedEntry :
    matrix = inverseCandidateMatrix_from_accumulatedEntry accumulatedInverseCandidateEntry
  sourceCandidateEntry_profile_eq_SM3cR_SM3dR_source :
    sourceCandidateEntry.candidate.profile =
      sourceCandidateEntry.candidate.profileData.profile
  exportStatus_eq :
    exportStatus =
      SM3db5RInverseCandidateMatrixExportStatus.inverseCandidateMatrixFromAccumulatedEntry
  sourceStatus_eq :
    sourceStatus =
      SM3db5RInverseCandidateMatrixSourceStatus.matrixEntriesFromSM3db4aRAccumulatedEntry
  noFreeMatrixStatus_eq :
    noFreeMatrixStatus = SM3db5RNoFreeMatrixStatus.noFreeMatrixOrEntryTable
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db5RNoMatrixInvStatus.noMatrixInvInSM3db5R
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noSM3daRInteriorBlockFallbackStatus_eq :
    noSM3daRInteriorBlockFallbackStatus =
      SM3db5RNoSM3daRInteriorBlockFallbackStatus.noSM3daRInteriorBlockFallback
  noProductProofStatus_eq :
    noProductProofStatus = SM3db5RNoProductProofStatus.noProductProofInSM3db5R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db5RNoTwoSidedInvStatus.noTwoSidedInvInSM3db5R
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3db5RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db5R
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db5RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db5R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db5RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db5R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db5RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db5R
  nextGateStatus_eq :
    nextGateStatus = SM3db5RNextGateStatus.sm3db6RShapeSeparationAfterMatrixExport

namespace GeneratedInteriorInverseCandidateMatrix

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

def fromAccumulatedEntry
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T where
  sourceCandidateEntry := E
  accumulatedInverseCandidateEntry :=
    GeneratedInteriorAccumulatedInverseCandidateEntry.fromAccumulatedTraceEvaluation T
  matrix :=
    inverseCandidateMatrix_from_accumulatedEntry
      (GeneratedInteriorAccumulatedInverseCandidateEntry.fromAccumulatedTraceEvaluation T)
  exportStatus :=
    SM3db5RInverseCandidateMatrixExportStatus.inverseCandidateMatrixFromAccumulatedEntry
  sourceStatus :=
    SM3db5RInverseCandidateMatrixSourceStatus.matrixEntriesFromSM3db4aRAccumulatedEntry
  noFreeMatrixStatus := SM3db5RNoFreeMatrixStatus.noFreeMatrixOrEntryTable
  noMatrixInvStatus := SM3db5RNoMatrixInvStatus.noMatrixInvInSM3db5R
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noSM3daRInteriorBlockFallbackStatus :=
    SM3db5RNoSM3daRInteriorBlockFallbackStatus.noSM3daRInteriorBlockFallback
  noProductProofStatus := SM3db5RNoProductProofStatus.noProductProofInSM3db5R
  noTwoSidedInvStatus := SM3db5RNoTwoSidedInvStatus.noTwoSidedInvInSM3db5R
  noInteriorEliminationCertificateStatus :=
    SM3db5RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db5R
  noInteriorEliminationDataStatus :=
    SM3db5RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db5R
  noDtnDataStatus :=
    SM3db5RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db5R
  noArithmeticTargetStatus :=
    SM3db5RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db5R
  nextGateStatus := SM3db5RNextGateStatus.sm3db6RShapeSeparationAfterMatrixExport
  sourceCandidateEntry_is_source := by
    rfl
  accumulatedInverseCandidateEntry_is_fromTrace := by
    rfl
  matrixEntry_from_accumulatedEntry := by
    intro i j
    rfl
  matrixEntry_from_accumulatedTraceValue := by
    intro i j
    exact
      (GeneratedInteriorAccumulatedInverseCandidateEntry.fromAccumulatedTraceEvaluation
        T).entry_eq_accumulatedTraceValue i j
  matrix_from_accumulatedEntry := by
    rfl
  sourceCandidateEntry_profile_eq_SM3cR_SM3dR_source :=
    E.candidateEntry_profile_eq_SM3dR_source
  exportStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  noFreeMatrixStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noSM3daRInteriorBlockFallbackStatus_eq := by
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

end GeneratedInteriorInverseCandidateMatrix

def inverseCandidateMatrix_from_inverseCandidateEntry
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
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ :=
  M.matrix

def inverseCandidateMatrix_from_eliminationTrace
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T :=
  GeneratedInteriorInverseCandidateMatrix.fromAccumulatedEntry T

theorem inverseCandidateMatrix_entry_eq_accumulatedEntry
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
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    M.matrix i j = M.accumulatedInverseCandidateEntry.entry i j :=
  M.matrixEntry_from_accumulatedEntry i j

theorem inverseCandidateMatrix_entry_eq_accumulatedTraceValue
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
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    M.matrix i j = generatedInteriorAccumulatedEntryValue T i j :=
  M.matrixEntry_from_accumulatedTraceValue i j

theorem inverseCandidateMatrix_entry_eq_inverseCandidateEntry
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
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    inverseCandidateMatrix_from_inverseCandidateEntry M i j =
      M.accumulatedInverseCandidateEntry.entry i j :=
  M.matrixEntry_from_accumulatedEntry i j

theorem inverseCandidate_profile_eq_SM3cR_SM3dR_source
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
    M.sourceCandidateEntry.candidate.profile =
      M.sourceCandidateEntry.candidate.profileData.profile :=
  M.sourceCandidateEntry_profile_eq_SM3cR_SM3dR_source

theorem noTwoSidedInv_for_SM3dbR
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
    M.noTwoSidedInvStatus = SM3db5RNoTwoSidedInvStatus.noTwoSidedInvInSM3db5R :=
  M.noTwoSidedInvStatus_eq

theorem noInteriorEliminationCertificate_for_SM3dbR
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
    M.noInteriorEliminationCertificateStatus =
      SM3db5RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db5R :=
  M.noInteriorEliminationCertificateStatus_eq

theorem noInteriorEliminationData_for_SM3dbR
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
    M.noInteriorEliminationDataStatus =
      SM3db5RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db5R :=
  M.noInteriorEliminationDataStatus_eq

theorem noMatrixInv_for_inverseCandidateMatrix
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
    M.noMatrixInvStatus = SM3db5RNoMatrixInvStatus.noMatrixInvInSM3db5R :=
  M.noMatrixInvStatus_eq

theorem noFreeMatrix_for_inverseCandidateMatrix
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
    M.noFreeMatrixStatus = SM3db5RNoFreeMatrixStatus.noFreeMatrixOrEntryTable :=
  M.noFreeMatrixStatus_eq

def regularGeneratedInteriorInverseCandidateMatrix
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorInverseCandidateMatrix
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp) :=
  inverseCandidateMatrix_from_eliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableGeneratedInteriorInverseCandidateMatrix
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorInverseCandidateMatrix
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp) :=
  inverseCandidateMatrix_from_eliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3db5RGeneratedInteriorInverseCandidateMatrixLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3db5RGeneratedInteriorInverseCandidateMatrixLedgerStatus
  sm3db4aRLedger :
    SM3db4aRGeneratedInteriorAccumulatedEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularMatrix :
    GeneratedInteriorInverseCandidateMatrix
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
  variableMatrix :
    GeneratedInteriorInverseCandidateMatrix
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
  sm3db4aRLedger_eq_main :
    sm3db4aRLedger =
      sm3db4aRGeneratedInteriorAccumulatedEntryLedger
        b β p regularWeight variableWeight regularPivot variablePivot
  regularMatrixEntryFromAccumulatedEntry :
    ∀ i j : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p),
      regularMatrix.matrix i j = regularMatrix.accumulatedInverseCandidateEntry.entry i j
  variableMatrixEntryFromAccumulatedEntry :
    ∀ i j : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p),
      variableMatrix.matrix i j = variableMatrix.accumulatedInverseCandidateEntry.entry i j
  regularNoFreeMatrix :
    regularMatrix.noFreeMatrixStatus = SM3db5RNoFreeMatrixStatus.noFreeMatrixOrEntryTable
  variableNoFreeMatrix :
    variableMatrix.noFreeMatrixStatus = SM3db5RNoFreeMatrixStatus.noFreeMatrixOrEntryTable
  regularNoMatrixInv :
    regularMatrix.noMatrixInvStatus = SM3db5RNoMatrixInvStatus.noMatrixInvInSM3db5R
  variableNoMatrixInv :
    variableMatrix.noMatrixInvStatus = SM3db5RNoMatrixInvStatus.noMatrixInvInSM3db5R
  regularNoSM3daRFallback :
    regularMatrix.noSM3daRInteriorBlockFallbackStatus =
      SM3db5RNoSM3daRInteriorBlockFallbackStatus.noSM3daRInteriorBlockFallback
  variableNoSM3daRFallback :
    variableMatrix.noSM3daRInteriorBlockFallbackStatus =
      SM3db5RNoSM3daRInteriorBlockFallbackStatus.noSM3daRInteriorBlockFallback
  regularNoProductProof :
    regularMatrix.noProductProofStatus = SM3db5RNoProductProofStatus.noProductProofInSM3db5R
  variableNoProductProof :
    variableMatrix.noProductProofStatus = SM3db5RNoProductProofStatus.noProductProofInSM3db5R
  regularNoTwoSidedInv :
    regularMatrix.noTwoSidedInvStatus = SM3db5RNoTwoSidedInvStatus.noTwoSidedInvInSM3db5R
  variableNoTwoSidedInv :
    variableMatrix.noTwoSidedInvStatus = SM3db5RNoTwoSidedInvStatus.noTwoSidedInvInSM3db5R
  regularNoInteriorEliminationCertificate :
    regularMatrix.noInteriorEliminationCertificateStatus =
      SM3db5RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db5R
  variableNoInteriorEliminationCertificate :
    variableMatrix.noInteriorEliminationCertificateStatus =
      SM3db5RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db5R
  regularNoInteriorEliminationData :
    regularMatrix.noInteriorEliminationDataStatus =
      SM3db5RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db5R
  variableNoInteriorEliminationData :
    variableMatrix.noInteriorEliminationDataStatus =
      SM3db5RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db5R
  regularNextGate :
    regularMatrix.nextGateStatus = SM3db5RNextGateStatus.sm3db6RShapeSeparationAfterMatrixExport
  variableNextGate :
    variableMatrix.nextGateStatus = SM3db5RNextGateStatus.sm3db6RShapeSeparationAfterMatrixExport
  status_eq_closed :
    status =
      SM3db5RGeneratedInteriorInverseCandidateMatrixLedgerStatus.generatedInteriorInverseCandidateMatrixExportClosed

def sm3db5RGeneratedInteriorInverseCandidateMatrixLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3db5RGeneratedInteriorInverseCandidateMatrixLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status :=
    SM3db5RGeneratedInteriorInverseCandidateMatrixLedgerStatus.generatedInteriorInverseCandidateMatrixExportClosed
  sm3db4aRLedger :=
    sm3db4aRGeneratedInteriorAccumulatedEntryLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularMatrix := regularGeneratedInteriorInverseCandidateMatrix b p regularWeight
  variableMatrix := variableGeneratedInteriorInverseCandidateMatrix β p variableWeight
  sm3db4aRLedger_eq_main := by
    rfl
  regularMatrixEntryFromAccumulatedEntry := by
    intro i j
    rfl
  variableMatrixEntryFromAccumulatedEntry := by
    intro i j
    rfl
  regularNoFreeMatrix := by
    rfl
  variableNoFreeMatrix := by
    rfl
  regularNoMatrixInv := by
    rfl
  variableNoMatrixInv := by
    rfl
  regularNoSM3daRFallback := by
    rfl
  variableNoSM3daRFallback := by
    rfl
  regularNoProductProof := by
    rfl
  variableNoProductProof := by
    rfl
  regularNoTwoSidedInv := by
    rfl
  variableNoTwoSidedInv := by
    rfl
  regularNoInteriorEliminationCertificate := by
    rfl
  variableNoInteriorEliminationCertificate := by
    rfl
  regularNoInteriorEliminationData := by
    rfl
  variableNoInteriorEliminationData := by
    rfl
  regularNextGate := by
    rfl
  variableNextGate := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3db5RGeneratedInteriorInverseCandidateMatrixLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db5RGeneratedInteriorInverseCandidateMatrixLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3db5RGeneratedInteriorInverseCandidateMatrixLedgerStatus.generatedInteriorInverseCandidateMatrixExportClosed := by
  rfl

theorem sm3db5RGeneratedInteriorInverseCandidateMatrixLedger_regularNoTwoSidedInv
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db5RGeneratedInteriorInverseCandidateMatrixLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularMatrix.noTwoSidedInvStatus =
      SM3db5RNoTwoSidedInvStatus.noTwoSidedInvInSM3db5R := by
  rfl

theorem sm3db5RGeneratedInteriorInverseCandidateMatrixLedger_regularNextGate
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db5RGeneratedInteriorInverseCandidateMatrixLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularMatrix.nextGateStatus =
      SM3db5RNextGateStatus.sm3db6RShapeSeparationAfterMatrixExport := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
