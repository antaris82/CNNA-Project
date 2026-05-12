import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3daRPositivePathLockStatus where
  | lockedBecauseCandidateEntryEqualsInteriorBlock
  deriving DecidableEq, Repr

inductive SM3dbRPositiveFirstContractStatus where
  | positiveCandidateChainStarted
  deriving DecidableEq, Repr

inductive SM3dbRNoStartObstructionStatus where
  | noObstructionBeforePositiveCarrierStepTraceAndCandidate
  deriving DecidableEq, Repr

inductive SM3dbRNewInverseCandidateRequirementStatus where
  | needsGeneratedInteriorInverseCandidateEntry
  deriving DecidableEq, Repr

inductive SM3dbRPrimaryOutputStatus where
  | noMatrixOptNoneAsPrimaryOutput
  deriving DecidableEq, Repr

inductive SM3dbRNoTwoSidedInvStatus where
  | noTwoSidedInvProofInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoMatrixInvStatus where
  | noMatrixInvInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoFreeInverseEntryTableStatus where
  | noFreeInverseEntryTableInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoExternalInverseOracleStatus where
  | noExternalInverseOracleInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db0R
  deriving DecidableEq, Repr

inductive SM3dbRNextPositivePhase where
  | sm3db1RGeneratedInteriorEliminationCarrier
  deriving DecidableEq, Repr

inductive SM3db0RPositiveFirstLedgerStatus where
  | sm3db0RPositiveFirstContractClosed
  deriving DecidableEq, Repr

structure SM3daRPositivePathLocked
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) where
  shapeAudit : GeneratedCandidateEntryShapeAudit Cell p A P wp W
  obstruction : GeneratedInteriorTwoSidedInvObstruction Cell p A P wp W E
  lockStatus : SM3daRPositivePathLockStatus
  shapeAudit_candidateEntry_eq : shapeAudit.candidateEntry = E
  obstruction_shapeAudit_eq : obstruction.shapeAudit = shapeAudit
  candidateEntry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      E.entry i j = generatedInteriorBlock W i j
  candidateMatrix_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix_from_candidateEntry E i j = generatedInteriorBlock W i j
  lockStatus_eq :
    lockStatus =
      SM3daRPositivePathLockStatus.lockedBecauseCandidateEntryEqualsInteriorBlock

namespace SM3daRPositivePathLocked

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}

def fromSM3eRShapeAudit
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    SM3daRPositivePathLocked Cell p A P wp W E where
  shapeAudit := GeneratedCandidateEntryShapeAudit.fromCandidateEntry E
  obstruction := generatedInteriorTwoSidedInvObstruction_fromShapeAudit E
  lockStatus :=
    SM3daRPositivePathLockStatus.lockedBecauseCandidateEntryEqualsInteriorBlock
  shapeAudit_candidateEntry_eq := by
    rfl
  obstruction_shapeAudit_eq := by
    rfl
  candidateEntry_eq_interiorBlock := by
    intro i j
    exact Smoke.candidateEntry_eq_interiorBlock E i j
  candidateMatrix_eq_interiorBlock := by
    intro i j
    exact Smoke.candidateMatrix_entry_eq_interiorBlock E i j
  lockStatus_eq := by
    rfl

theorem locked_status
    (L : SM3daRPositivePathLocked Cell p A P wp W E) :
    L.lockStatus =
      SM3daRPositivePathLockStatus.lockedBecauseCandidateEntryEqualsInteriorBlock :=
  L.lockStatus_eq

theorem entry_eq_interiorBlock
    (L : SM3daRPositivePathLocked Cell p A P wp W E)
    (i j : GeneratedInteriorIndex A) :
    E.entry i j = generatedInteriorBlock W i j :=
  L.candidateEntry_eq_interiorBlock i j

theorem matrix_eq_interiorBlock
    (L : SM3daRPositivePathLocked Cell p A P wp W E)
    (i j : GeneratedInteriorIndex A) :
    candidateMatrix_from_candidateEntry E i j = generatedInteriorBlock W i j :=
  L.candidateMatrix_eq_interiorBlock i j

end SM3daRPositivePathLocked

structure SM3dbRPositiveFirstContract
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) where
  sm3daRLock : SM3daRPositivePathLocked Cell p A P wp W E
  contractStatus : SM3dbRPositiveFirstContractStatus
  noStartObstructionStatus : SM3dbRNoStartObstructionStatus
  newInverseCandidateRequirementStatus :
    SM3dbRNewInverseCandidateRequirementStatus
  primaryOutputStatus : SM3dbRPrimaryOutputStatus
  noTwoSidedInvStatus : SM3dbRNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus :
    SM3dbRNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3dbRNoInteriorEliminationDataStatus
  noMatrixInvStatus : SM3dbRNoMatrixInvStatus
  noFreeInverseEntryTableStatus : SM3dbRNoFreeInverseEntryTableStatus
  noExternalInverseOracleStatus : SM3dbRNoExternalInverseOracleStatus
  noDtnDataStatus : SM3dbRNoDtnDataStatus
  noArithmeticTargetStatus : SM3dbRNoArithmeticTargetStatus
  nextPositivePhase : SM3dbRNextPositivePhase
  sm3daRLock_eq_main :
    sm3daRLock = SM3daRPositivePathLocked.fromSM3eRShapeAudit E
  sm3daR_entry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      E.entry i j = generatedInteriorBlock W i j
  sm3daR_matrix_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix_from_candidateEntry E i j = generatedInteriorBlock W i j
  contractStatus_eq :
    contractStatus = SM3dbRPositiveFirstContractStatus.positiveCandidateChainStarted
  noStartObstructionStatus_eq :
    noStartObstructionStatus =
      SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate
  newInverseCandidateRequirementStatus_eq :
    newInverseCandidateRequirementStatus =
      SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry
  primaryOutputStatus_eq :
    primaryOutputStatus = SM3dbRPrimaryOutputStatus.noMatrixOptNoneAsPrimaryOutput
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3dbRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3db0R
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3dbRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db0R
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3dbRNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db0R
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3dbRNoMatrixInvStatus.noMatrixInvInSM3db0R
  noFreeInverseEntryTableStatus_eq :
    noFreeInverseEntryTableStatus =
      SM3dbRNoFreeInverseEntryTableStatus.noFreeInverseEntryTableInSM3db0R
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3dbRNoExternalInverseOracleStatus.noExternalInverseOracleInSM3db0R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3dbRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3dbRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db0R
  nextPositivePhase_eq :
    nextPositivePhase =
      SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier

namespace SM3dbRPositiveFirstContract

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}

def fromSM3daRLock
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    SM3dbRPositiveFirstContract Cell p A P wp W E where
  sm3daRLock := SM3daRPositivePathLocked.fromSM3eRShapeAudit E
  contractStatus := SM3dbRPositiveFirstContractStatus.positiveCandidateChainStarted
  noStartObstructionStatus :=
    SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate
  newInverseCandidateRequirementStatus :=
    SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry
  primaryOutputStatus := SM3dbRPrimaryOutputStatus.noMatrixOptNoneAsPrimaryOutput
  noTwoSidedInvStatus := SM3dbRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3db0R
  noInteriorEliminationCertificateStatus :=
    SM3dbRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db0R
  noInteriorEliminationDataStatus :=
    SM3dbRNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db0R
  noMatrixInvStatus := SM3dbRNoMatrixInvStatus.noMatrixInvInSM3db0R
  noFreeInverseEntryTableStatus :=
    SM3dbRNoFreeInverseEntryTableStatus.noFreeInverseEntryTableInSM3db0R
  noExternalInverseOracleStatus :=
    SM3dbRNoExternalInverseOracleStatus.noExternalInverseOracleInSM3db0R
  noDtnDataStatus :=
    SM3dbRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R
  noArithmeticTargetStatus :=
    SM3dbRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db0R
  nextPositivePhase :=
    SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier
  sm3daRLock_eq_main := by
    rfl
  sm3daR_entry_eq_interiorBlock := by
    intro i j
    exact Smoke.candidateEntry_eq_interiorBlock E i j
  sm3daR_matrix_eq_interiorBlock := by
    intro i j
    exact Smoke.candidateMatrix_entry_eq_interiorBlock E i j
  contractStatus_eq := by
    rfl
  noStartObstructionStatus_eq := by
    rfl
  newInverseCandidateRequirementStatus_eq := by
    rfl
  primaryOutputStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noFreeInverseEntryTableStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPositivePhase_eq := by
    rfl

theorem no_obstruction_start
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.noStartObstructionStatus =
      SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate :=
  C.noStartObstructionStatus_eq

theorem needs_new_inverse_candidate_entry
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.newInverseCandidateRequirementStatus =
      SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry :=
  C.newInverseCandidateRequirementStatus_eq

theorem no_primary_matrixOpt_none
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.primaryOutputStatus = SM3dbRPrimaryOutputStatus.noMatrixOptNoneAsPrimaryOutput :=
  C.primaryOutputStatus_eq

theorem next_phase_is_carrier
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.nextPositivePhase =
      SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier :=
  C.nextPositivePhase_eq

theorem noTwoSidedInv
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.noTwoSidedInvStatus =
      SM3dbRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3db0R :=
  C.noTwoSidedInvStatus_eq

theorem noInteriorEliminationCertificate
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.noInteriorEliminationCertificateStatus =
      SM3dbRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db0R :=
  C.noInteriorEliminationCertificateStatus_eq

theorem noDtnData
    (C : SM3dbRPositiveFirstContract Cell p A P wp W E) :
    C.noDtnDataStatus =
      SM3dbRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R :=
  C.noDtnDataStatus_eq

end SM3dbRPositiveFirstContract

def sm3daRPositivePathLocked
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    SM3daRPositivePathLocked Cell p A P wp W E :=
  SM3daRPositivePathLocked.fromSM3eRShapeAudit E

def sm3dbRPositiveFirstContract
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    SM3dbRPositiveFirstContract Cell p A P wp W E :=
  SM3dbRPositiveFirstContract.fromSM3daRLock E

def regularSM3daRPositivePathLocked
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    SM3daRPositivePathLocked
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp) :=
  sm3daRPositivePathLocked
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)

def variableSM3daRPositivePathLocked
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    SM3daRPositivePathLocked
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp) :=
  sm3daRPositivePathLocked
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)

def regularSM3dbRPositiveFirstContract
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    SM3dbRPositiveFirstContract
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp) :=
  sm3dbRPositiveFirstContract
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)

def variableSM3dbRPositiveFirstContract
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    SM3dbRPositiveFirstContract
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp) :=
  sm3dbRPositiveFirstContract
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)

structure SM3db0RPositiveFirstLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3db0RPositiveFirstLedgerStatus
  sm3eRLedger : SM3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight
  regularLock :
    SM3daRPositivePathLocked
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
  variableLock :
    SM3daRPositivePathLocked
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
  regularContract :
    SM3dbRPositiveFirstContract
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
  variableContract :
    SM3dbRPositiveFirstContract
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
  sm3eRLedger_eq_main :
    sm3eRLedger = sm3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight
  regularLock_eq_main :
    regularLock = regularSM3daRPositivePathLocked b p regularWeight
  variableLock_eq_main :
    variableLock = variableSM3daRPositivePathLocked β p variableWeight
  regularContract_eq_main :
    regularContract = regularSM3dbRPositiveFirstContract b p regularWeight
  variableContract_eq_main :
    variableContract = variableSM3dbRPositiveFirstContract β p variableWeight
  regularNoStartObstruction :
    regularContract.noStartObstructionStatus =
      SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate
  variableNoStartObstruction :
    variableContract.noStartObstructionStatus =
      SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate
  regularNeedsNewInverseCandidateEntry :
    regularContract.newInverseCandidateRequirementStatus =
      SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry
  variableNeedsNewInverseCandidateEntry :
    variableContract.newInverseCandidateRequirementStatus =
      SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry
  regularNextPositivePhase :
    regularContract.nextPositivePhase =
      SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier
  variableNextPositivePhase :
    variableContract.nextPositivePhase =
      SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier
  regularNoTwoSidedInv :
    regularContract.noTwoSidedInvStatus =
      SM3dbRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3db0R
  variableNoTwoSidedInv :
    variableContract.noTwoSidedInvStatus =
      SM3dbRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3db0R
  regularNoDtnData :
    regularContract.noDtnDataStatus =
      SM3dbRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R
  variableNoDtnData :
    variableContract.noDtnDataStatus =
      SM3dbRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R
  status_eq_closed :
    status = SM3db0RPositiveFirstLedgerStatus.sm3db0RPositiveFirstContractClosed

def sm3db0RPositiveFirstLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3db0RPositiveFirstLedger b β p regularWeight variableWeight where
  status := SM3db0RPositiveFirstLedgerStatus.sm3db0RPositiveFirstContractClosed
  sm3eRLedger := sm3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight
  regularLock := regularSM3daRPositivePathLocked b p regularWeight
  variableLock := variableSM3daRPositivePathLocked β p variableWeight
  regularContract := regularSM3dbRPositiveFirstContract b p regularWeight
  variableContract := variableSM3dbRPositiveFirstContract β p variableWeight
  sm3eRLedger_eq_main := by
    rfl
  regularLock_eq_main := by
    rfl
  variableLock_eq_main := by
    rfl
  regularContract_eq_main := by
    rfl
  variableContract_eq_main := by
    rfl
  regularNoStartObstruction := by
    rfl
  variableNoStartObstruction := by
    rfl
  regularNeedsNewInverseCandidateEntry := by
    rfl
  variableNeedsNewInverseCandidateEntry := by
    rfl
  regularNextPositivePhase := by
    rfl
  variableNextPositivePhase := by
    rfl
  regularNoTwoSidedInv := by
    rfl
  variableNoTwoSidedInv := by
    rfl
  regularNoDtnData := by
    rfl
  variableNoDtnData := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3daRPositivePathLocked_status
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    (sm3daRPositivePathLocked E).lockStatus =
      SM3daRPositivePathLockStatus.lockedBecauseCandidateEntryEqualsInteriorBlock := by
  rfl

theorem noSM3dbRStartsWithObstruction
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    (sm3dbRPositiveFirstContract E).noStartObstructionStatus =
      SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate := by
  rfl

theorem SM3dbRNeedsNewInverseCandidateEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    (sm3dbRPositiveFirstContract E).newInverseCandidateRequirementStatus =
      SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry := by
  rfl

theorem sm3db0RPositiveFirstLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db0RPositiveFirstLedger b β p regularWeight variableWeight).status =
      SM3db0RPositiveFirstLedgerStatus.sm3db0RPositiveFirstContractClosed := by
  rfl

theorem sm3db0RPositiveFirstLedger_regularNoStartObstruction
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db0RPositiveFirstLedger b β p regularWeight variableWeight).regularContract.noStartObstructionStatus =
      SM3dbRNoStartObstructionStatus.noObstructionBeforePositiveCarrierStepTraceAndCandidate := by
  rfl

theorem sm3db0RPositiveFirstLedger_variableNeedsNewInverseCandidateEntry
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db0RPositiveFirstLedger b β p regularWeight variableWeight).variableContract.newInverseCandidateRequirementStatus =
      SM3dbRNewInverseCandidateRequirementStatus.needsGeneratedInteriorInverseCandidateEntry := by
  rfl

theorem sm3db0RPositiveFirstLedger_regularNextPositivePhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db0RPositiveFirstLedger b β p regularWeight variableWeight).regularContract.nextPositivePhase =
      SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier := by
  rfl

theorem sm3db0RPositiveFirstLedger_variableNoDtnData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db0RPositiveFirstLedger b β p regularWeight variableWeight).variableContract.noDtnDataStatus =
      SM3dbRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db0R := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
