import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive GeneratedInteriorEliminationCandidateEntrySource where
  | entryFromTreeRecursiveProfile
  deriving DecidableEq, Repr

inductive SM3daRCandidateEntryInterfaceStatus where
  | candidateEntryInterfaceFromSM3dRCandidate
  deriving DecidableEq, Repr

inductive SM3daRCandidateEntryValidationStatus where
  | entryNotValidatedUntilSM3eRProductProofs
  deriving DecidableEq, Repr

inductive SM3daRNoMatrixInvStatus where
  | noMatrixInvForCandidateEntry
  deriving DecidableEq, Repr

inductive SM3daRNoFreeEntryTableStatus where
  | noFreeEntryTable
  deriving DecidableEq, Repr

inductive SM3daRNoExternalInverseOracleStatus where
  | noExternalInverseOracle
  deriving DecidableEq, Repr

inductive SM3daRNoTwoSidedInvStatus where
  | noTwoSidedInvProofInSM3daR
  deriving DecidableEq, Repr

inductive SM3daRNoExternalInteriorEliminationCertificateStatus where
  | noExternalInteriorEliminationCertificateAssumption
  deriving DecidableEq, Repr

inductive SM3daRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataYet
  deriving DecidableEq, Repr

inductive SM3daRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3daR
  deriving DecidableEq, Repr

inductive SM3daRGeneratedInteriorEliminationCandidateEntryLedgerStatus where
  | generatedCandidateEntryInterfaceBuiltFromSM3dRCandidates
  deriving DecidableEq, Repr

def generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  match C.source with
  | GeneratedInteriorEliminationCandidateSource.candidateFromDiagonalOnly =>
      generatedInteriorBlock W i j
  | GeneratedInteriorEliminationCandidateSource.candidateFromDegreeDiagonal =>
      generatedInteriorBlock W i j
  | GeneratedInteriorEliminationCandidateSource.candidateFromOffdiagCoupledProfile =>
      generatedInteriorBlock W i j
  | GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile =>
      generatedInteriorBlock W i j
  | GeneratedInteriorEliminationCandidateSource.candidateFromGeneralFiniteEliminationProfile =>
      generatedInteriorBlock W i j
  | GeneratedInteriorEliminationCandidateSource.candidateObstructed =>
      generatedInteriorBlock W i j

def generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_matrix
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ :=
  fun i j => generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value C i j

structure GeneratedInteriorEliminationCandidateEntry
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) where
  candidate : GeneratedInteriorEliminationCandidate Cell p A P wp W
  source : GeneratedInteriorEliminationCandidateEntrySource
  entry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  matrix : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ
  interfaceStatus : SM3daRCandidateEntryInterfaceStatus
  validationStatus : SM3daRCandidateEntryValidationStatus
  noMatrixInvStatus : SM3daRNoMatrixInvStatus
  noFreeEntryTableStatus : SM3daRNoFreeEntryTableStatus
  noExternalInverseOracleStatus : SM3daRNoExternalInverseOracleStatus
  noTwoSidedInvStatus : SM3daRNoTwoSidedInvStatus
  noExternalInteriorEliminationCertificateStatus :
    SM3daRNoExternalInteriorEliminationCertificateStatus
  noDtnDataStatus : SM3daRNoDtnDataStatus
  noArithmeticTargetStatus : SM3daRNoArithmeticTargetStatus
  candidateSource_treeRecursive :
    candidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
  source_eq_treeRecursive :
    source = GeneratedInteriorEliminationCandidateEntrySource.entryFromTreeRecursiveProfile
  entry_eq_from_treeRecursiveProfile :
    ∀ i j : GeneratedInteriorIndex A,
      entry i j =
        generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value
          candidate i j
  matrix_eq_from_candidateEntry :
    ∀ i j : GeneratedInteriorIndex A,
      matrix i j = entry i j
  candidateEntry_profile_eq_SM3dR_source :
    candidate.profile = candidate.profileData.profile
  interfaceStatus_eq :
    interfaceStatus =
      SM3daRCandidateEntryInterfaceStatus.candidateEntryInterfaceFromSM3dRCandidate
  validationStatus_eq :
    validationStatus =
      SM3daRCandidateEntryValidationStatus.entryNotValidatedUntilSM3eRProductProofs
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3daRNoMatrixInvStatus.noMatrixInvForCandidateEntry
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3daRNoFreeEntryTableStatus.noFreeEntryTable
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3daRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3daR
  noExternalInteriorEliminationCertificateStatus_eq :
    noExternalInteriorEliminationCertificateStatus =
      SM3daRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3daRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3daRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3daR

namespace GeneratedInteriorEliminationCandidateEntry

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}

def fromTreeRecursiveCandidate
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (hC : C.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile) :
    GeneratedInteriorEliminationCandidateEntry Cell p A P wp W where
  candidate := C
  source := GeneratedInteriorEliminationCandidateEntrySource.entryFromTreeRecursiveProfile
  entry := fun i j =>
    generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value C i j
  matrix := generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_matrix C
  interfaceStatus :=
    SM3daRCandidateEntryInterfaceStatus.candidateEntryInterfaceFromSM3dRCandidate
  validationStatus :=
    SM3daRCandidateEntryValidationStatus.entryNotValidatedUntilSM3eRProductProofs
  noMatrixInvStatus := SM3daRNoMatrixInvStatus.noMatrixInvForCandidateEntry
  noFreeEntryTableStatus := SM3daRNoFreeEntryTableStatus.noFreeEntryTable
  noExternalInverseOracleStatus := SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle
  noTwoSidedInvStatus := SM3daRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3daR
  noExternalInteriorEliminationCertificateStatus :=
    SM3daRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  noDtnDataStatus := SM3daRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  noArithmeticTargetStatus :=
    SM3daRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3daR
  candidateSource_treeRecursive := hC
  source_eq_treeRecursive := by
    rfl
  entry_eq_from_treeRecursiveProfile := by
    intro i j
    rfl
  matrix_eq_from_candidateEntry := by
    intro i j
    rfl
  candidateEntry_profile_eq_SM3dR_source :=
    C.profile_eq_SM3cR_profile
  interfaceStatus_eq := by
    rfl
  validationStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noExternalInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

theorem noMatrixInv_for_candidateEntry
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noMatrixInvStatus = SM3daRNoMatrixInvStatus.noMatrixInvForCandidateEntry :=
  E.noMatrixInvStatus_eq

theorem noFreeEntryTable
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noFreeEntryTableStatus = SM3daRNoFreeEntryTableStatus.noFreeEntryTable :=
  E.noFreeEntryTableStatus_eq

theorem noExternalInverseOracle
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noExternalInverseOracleStatus =
      SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle :=
  E.noExternalInverseOracleStatus_eq

theorem noTwoSidedInv
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noTwoSidedInvStatus = SM3daRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3daR :=
  E.noTwoSidedInvStatus_eq

theorem noExternalInteriorEliminationCertificate
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noExternalInteriorEliminationCertificateStatus =
      SM3daRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption :=
  E.noExternalInteriorEliminationCertificateStatus_eq

theorem noDtnDataYet
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noDtnDataStatus = SM3daRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet :=
  E.noDtnDataStatus_eq

theorem noArithmeticTarget
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noArithmeticTargetStatus =
      SM3daRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3daR :=
  E.noArithmeticTargetStatus_eq

theorem matrix_entry
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    E.matrix i j = E.entry i j :=
  E.matrix_eq_from_candidateEntry i j

end GeneratedInteriorEliminationCandidateEntry

def candidateEntry_from_treeRecursiveProfile
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (hC : C.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile) :
    GeneratedInteriorEliminationCandidateEntry Cell p A P wp W :=
  GeneratedInteriorEliminationCandidateEntry.fromTreeRecursiveCandidate C hC

def candidateMatrix_from_candidateEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ :=
  E.matrix

theorem candidateMatrix_from_candidateEntry_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    candidateMatrix_from_candidateEntry E i j = E.entry i j :=
  E.matrix_eq_from_candidateEntry i j

theorem candidateEntry_profile_eq_SM3dR_source
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.candidate.profile = E.candidate.profileData.profile :=
  E.candidateEntry_profile_eq_SM3dR_source

theorem noMatrixInv_for_candidateEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noMatrixInvStatus = SM3daRNoMatrixInvStatus.noMatrixInvForCandidateEntry :=
  E.noMatrixInvStatus_eq

theorem noFreeEntryTable
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noFreeEntryTableStatus = SM3daRNoFreeEntryTableStatus.noFreeEntryTable :=
  E.noFreeEntryTableStatus_eq

theorem noExternalInverseOracle
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    E.noExternalInverseOracleStatus =
      SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle :=
  E.noExternalInverseOracleStatus_eq

def regularGeneratedInteriorEliminationCandidateEntry
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationCandidateEntry
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp) :=
  candidateEntry_from_treeRecursiveProfile
    (regularGeneratedInteriorEliminationCandidate b p wp)
    (by rfl)

def variableGeneratedInteriorEliminationCandidateEntry
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationCandidateEntry
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp) :=
  candidateEntry_from_treeRecursiveProfile
    (variableGeneratedInteriorEliminationCandidate β p wp)
    (by rfl)

structure SM3daRGeneratedInteriorEliminationCandidateEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3daRGeneratedInteriorEliminationCandidateEntryLedgerStatus
  sm3dLedger : SM3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight
  regularCandidateEntry :
    GeneratedInteriorEliminationCandidateEntry
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variableCandidateEntry :
    GeneratedInteriorEliminationCandidateEntry
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  sm3dLedger_eq_main :
    sm3dLedger = sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight
  regularCandidateEntry_eq_main :
    regularCandidateEntry = regularGeneratedInteriorEliminationCandidateEntry b p regularWeight
  variableCandidateEntry_eq_main :
    variableCandidateEntry = variableGeneratedInteriorEliminationCandidateEntry β p variableWeight
  regularCandidateSource_treeRecursive :
    regularCandidateEntry.candidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
  variableCandidateSource_treeRecursive :
    variableCandidateEntry.candidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
  regularCandidateMatrix_from_candidateEntry :
    ∀ i j : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p),
      candidateMatrix_from_candidateEntry regularCandidateEntry i j =
        regularCandidateEntry.entry i j
  variableCandidateMatrix_from_candidateEntry :
    ∀ i j : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p),
      candidateMatrix_from_candidateEntry variableCandidateEntry i j =
        variableCandidateEntry.entry i j
  regularProfile_eq_SM3dR_source :
    regularCandidateEntry.candidate.profile =
      regularCandidateEntry.candidate.profileData.profile
  variableProfile_eq_SM3dR_source :
    variableCandidateEntry.candidate.profile =
      variableCandidateEntry.candidate.profileData.profile
  regularNoMatrixInv :
    regularCandidateEntry.noMatrixInvStatus =
      SM3daRNoMatrixInvStatus.noMatrixInvForCandidateEntry
  variableNoMatrixInv :
    variableCandidateEntry.noMatrixInvStatus =
      SM3daRNoMatrixInvStatus.noMatrixInvForCandidateEntry
  regularNoFreeEntryTable :
    regularCandidateEntry.noFreeEntryTableStatus =
      SM3daRNoFreeEntryTableStatus.noFreeEntryTable
  variableNoFreeEntryTable :
    variableCandidateEntry.noFreeEntryTableStatus =
      SM3daRNoFreeEntryTableStatus.noFreeEntryTable
  regularNoExternalInverseOracle :
    regularCandidateEntry.noExternalInverseOracleStatus =
      SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle
  variableNoExternalInverseOracle :
    variableCandidateEntry.noExternalInverseOracleStatus =
      SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle
  regularNoTwoSidedInv :
    regularCandidateEntry.noTwoSidedInvStatus =
      SM3daRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3daR
  variableNoTwoSidedInv :
    variableCandidateEntry.noTwoSidedInvStatus =
      SM3daRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3daR
  regularNoExternalInteriorEliminationCertificate :
    regularCandidateEntry.noExternalInteriorEliminationCertificateStatus =
      SM3daRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  variableNoExternalInteriorEliminationCertificate :
    variableCandidateEntry.noExternalInteriorEliminationCertificateStatus =
      SM3daRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  regularNoDtnDataYet :
    regularCandidateEntry.noDtnDataStatus =
      SM3daRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  variableNoDtnDataYet :
    variableCandidateEntry.noDtnDataStatus =
      SM3daRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  regularNoArithmeticTarget :
    regularCandidateEntry.noArithmeticTargetStatus =
      SM3daRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3daR
  variableNoArithmeticTarget :
    variableCandidateEntry.noArithmeticTargetStatus =
      SM3daRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3daR
  status_eq_closed :
    status =
      SM3daRGeneratedInteriorEliminationCandidateEntryLedgerStatus.generatedCandidateEntryInterfaceBuiltFromSM3dRCandidates

def sm3daRGeneratedInteriorEliminationCandidateEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight where
  status :=
    SM3daRGeneratedInteriorEliminationCandidateEntryLedgerStatus.generatedCandidateEntryInterfaceBuiltFromSM3dRCandidates
  sm3dLedger := sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight
  regularCandidateEntry := regularGeneratedInteriorEliminationCandidateEntry b p regularWeight
  variableCandidateEntry := variableGeneratedInteriorEliminationCandidateEntry β p variableWeight
  sm3dLedger_eq_main := by
    rfl
  regularCandidateEntry_eq_main := by
    rfl
  variableCandidateEntry_eq_main := by
    rfl
  regularCandidateSource_treeRecursive := by
    rfl
  variableCandidateSource_treeRecursive := by
    rfl
  regularCandidateMatrix_from_candidateEntry := by
    intro i j
    rfl
  variableCandidateMatrix_from_candidateEntry := by
    intro i j
    rfl
  regularProfile_eq_SM3dR_source := by
    rfl
  variableProfile_eq_SM3dR_source := by
    rfl
  regularNoMatrixInv := by
    rfl
  variableNoMatrixInv := by
    rfl
  regularNoFreeEntryTable := by
    rfl
  variableNoFreeEntryTable := by
    rfl
  regularNoExternalInverseOracle := by
    rfl
  variableNoExternalInverseOracle := by
    rfl
  regularNoTwoSidedInv := by
    rfl
  variableNoTwoSidedInv := by
    rfl
  regularNoExternalInteriorEliminationCertificate := by
    rfl
  variableNoExternalInteriorEliminationCertificate := by
    rfl
  regularNoDtnDataYet := by
    rfl
  variableNoDtnDataYet := by
    rfl
  regularNoArithmeticTarget := by
    rfl
  variableNoArithmeticTarget := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3daRGeneratedInteriorEliminationCandidateEntryLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight).status =
      SM3daRGeneratedInteriorEliminationCandidateEntryLedgerStatus.generatedCandidateEntryInterfaceBuiltFromSM3dRCandidates := by
  rfl

theorem sm3daRGeneratedInteriorEliminationCandidateEntryLedger_regularNoFreeEntryTable
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight).regularCandidateEntry.noFreeEntryTableStatus =
      SM3daRNoFreeEntryTableStatus.noFreeEntryTable := by
  rfl

theorem sm3daRGeneratedInteriorEliminationCandidateEntryLedger_variableNoExternalInverseOracle
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight).variableCandidateEntry.noExternalInverseOracleStatus =
      SM3daRNoExternalInverseOracleStatus.noExternalInverseOracle := by
  rfl

theorem sm3daRGeneratedInteriorEliminationCandidateEntryLedger_regularNoTwoSidedInv
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight).regularCandidateEntry.noTwoSidedInvStatus =
      SM3daRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3daR := by
  rfl

theorem sm3daRGeneratedInteriorEliminationCandidateEntryLedger_variableNoDtnDataYet
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight).variableCandidateEntry.noDtnDataStatus =
      SM3daRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
