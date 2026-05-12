import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db1RNodeOriginStatus where
  | nodeFromGeneratedInteriorIndexAndPartition
  deriving DecidableEq, Repr

inductive SM3db1RProfileSourceStatus where
  | profileFromSM3cRInteriorBlockStructure
  deriving DecidableEq, Repr

inductive SM3db1RCandidateSourceStatus where
  | candidateFromSM3dRStructureDependentCandidate
  deriving DecidableEq, Repr

inductive SM3db1RDepthStatus where
  | depthFromGeneratedInteriorLevel
  deriving DecidableEq, Repr

inductive SM3db1RMeasureStatus where
  | measureFromCutoffMinusInteriorDepth
  deriving DecidableEq, Repr

inductive SM3db1RCarrierStatus where
  | generatedInteriorEliminationCarrierClosed
  deriving DecidableEq, Repr

inductive SM3db1RNoFreeEliminationCarrierStatus where
  | noFreeEliminationCarrier
  deriving DecidableEq, Repr

inductive SM3db1RNoExternalEliminationOrderOracleStatus where
  | noExternalEliminationOrderOracle
  deriving DecidableEq, Repr

inductive SM3db1RNoFreePivotListStatus where
  | noFreePivotList
  deriving DecidableEq, Repr

inductive SM3db1RNoInverseEntryFunctionStatus where
  | noInverseEntryFunctionInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoMatrixExportStatus where
  | noMatrixExportInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoEliminationTraceStatus where
  | noEliminationTraceInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoMatrixInvStatus where
  | noMatrixInvInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db1R
  deriving DecidableEq, Repr

inductive SM3db1RNextPositivePhase where
  | sm3db2RGeneratedInteriorEliminationStep
  deriving DecidableEq, Repr

inductive SM3db1RGeneratedInteriorEliminationCarrierLedgerStatus where
  | generatedInteriorEliminationCarrierClosed
  deriving DecidableEq, Repr

structure GeneratedInteriorEliminationNode
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) where
  index : GeneratedInteriorIndex A
  approximantIndex : GeneratedApproximantIndex A
  approximantIndex_eq_index :
    approximantIndex = GeneratedInteriorIndex.toApproximantIndex index
  interiorMembership : approximantIndex ∈ P.interiorCarrier
  profileData : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  candidate : GeneratedInteriorEliminationCandidate Cell p A P wp W
  nodeOriginStatus : SM3db1RNodeOriginStatus
  profileSourceStatus : SM3db1RProfileSourceStatus
  candidateSourceStatus : SM3db1RCandidateSourceStatus
  profileData_eq_candidateProfileData : profileData = C.profileData
  candidate_eq : candidate = C
  candidate_profile_eq_profileData : candidate.profile = profileData.profile
  candidate_sourceCompatible :
    GeneratedInteriorEliminationCandidateSourceCompatible
      candidate.source profileData.profile
  nodeOriginStatus_eq :
    nodeOriginStatus =
      SM3db1RNodeOriginStatus.nodeFromGeneratedInteriorIndexAndPartition
  profileSourceStatus_eq :
    profileSourceStatus =
      SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure
  candidateSourceStatus_eq :
    candidateSourceStatus =
      SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate

namespace GeneratedInteriorEliminationNode

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {C : GeneratedInteriorEliminationCandidate Cell p A P wp W}

def fromInteriorIndex
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorEliminationNode Cell p A P wp W C where
  index := i
  approximantIndex := GeneratedInteriorIndex.toApproximantIndex i
  approximantIndex_eq_index := by
    rfl
  interiorMembership := by
    rw [P.interiorCarrier_eq]
    exact interior_mem_interiorCarrier i
  profileData := C.profileData
  candidate := C
  nodeOriginStatus :=
    SM3db1RNodeOriginStatus.nodeFromGeneratedInteriorIndexAndPartition
  profileSourceStatus :=
    SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure
  candidateSourceStatus :=
    SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate
  profileData_eq_candidateProfileData := by
    rfl
  candidate_eq := by
    rfl
  candidate_profile_eq_profileData :=
    C.profile_eq_SM3cR_profile
  candidate_sourceCompatible :=
    C.sourceCompatible
  nodeOriginStatus_eq := by
    rfl
  profileSourceStatus_eq := by
    rfl
  candidateSourceStatus_eq := by
    rfl

theorem index_membership
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C) :
    N.approximantIndex ∈ P.interiorCarrier :=
  N.interiorMembership

theorem candidate_profile_eq_nodeProfileData
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C) :
    N.candidate.profile = N.profileData.profile :=
  N.candidate_profile_eq_profileData

theorem node_from_SM3cR_SM3dR
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C) :
    N.profileSourceStatus =
        SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure ∧
      N.candidateSourceStatus =
        SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate :=
  And.intro N.profileSourceStatus_eq N.candidateSourceStatus_eq

end GeneratedInteriorEliminationNode

structure GeneratedInteriorEliminationDepth
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C) where
  depth : Nat
  depthStatus : SM3db1RDepthStatus
  depth_eq_index_level :
    depth = (GeneratedInteriorIndex.level N.index).val
  depth_lt_cutoff : depth < p.L_max
  depthStatus_eq :
    depthStatus = SM3db1RDepthStatus.depthFromGeneratedInteriorLevel

namespace GeneratedInteriorEliminationDepth

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {C : GeneratedInteriorEliminationCandidate Cell p A P wp W}
variable {N : GeneratedInteriorEliminationNode Cell p A P wp W C}

def fromNode
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C) :
    GeneratedInteriorEliminationDepth Cell p A P wp W C N where
  depth := (GeneratedInteriorIndex.level N.index).val
  depthStatus := SM3db1RDepthStatus.depthFromGeneratedInteriorLevel
  depth_eq_index_level := by
    rfl
  depth_lt_cutoff :=
    GeneratedInteriorIndex.level_lt_cutoff N.index
  depthStatus_eq := by
    rfl

theorem depth_from_index_level
    (D : GeneratedInteriorEliminationDepth Cell p A P wp W C N) :
    D.depth = (GeneratedInteriorIndex.level N.index).val :=
  D.depth_eq_index_level

theorem depth_is_interior
    (D : GeneratedInteriorEliminationDepth Cell p A P wp W C N) :
    D.depth < p.L_max :=
  D.depth_lt_cutoff

end GeneratedInteriorEliminationDepth

structure GeneratedInteriorEliminationMeasure
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C)
    (D : GeneratedInteriorEliminationDepth Cell p A P wp W C N) where
  measure : Nat
  measureStatus : SM3db1RMeasureStatus
  measure_eq_cutoff_sub_depth : measure = p.L_max - D.depth
  depth_lt_cutoff : D.depth < p.L_max
  measureStatus_eq :
    measureStatus = SM3db1RMeasureStatus.measureFromCutoffMinusInteriorDepth

namespace GeneratedInteriorEliminationMeasure

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {C : GeneratedInteriorEliminationCandidate Cell p A P wp W}
variable {N : GeneratedInteriorEliminationNode Cell p A P wp W C}
variable {D : GeneratedInteriorEliminationDepth Cell p A P wp W C N}

def fromDepth
    (D : GeneratedInteriorEliminationDepth Cell p A P wp W C N) :
    GeneratedInteriorEliminationMeasure Cell p A P wp W C N D where
  measure := p.L_max - D.depth
  measureStatus := SM3db1RMeasureStatus.measureFromCutoffMinusInteriorDepth
  measure_eq_cutoff_sub_depth := by
    rfl
  depth_lt_cutoff :=
    D.depth_lt_cutoff
  measureStatus_eq := by
    rfl

theorem measure_from_depth
    (M : GeneratedInteriorEliminationMeasure Cell p A P wp W C N D) :
    M.measure = p.L_max - D.depth :=
  M.measure_eq_cutoff_sub_depth

end GeneratedInteriorEliminationMeasure

def generatedInteriorEliminationNode_fromIndex
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorEliminationNode Cell p A P wp W C :=
  GeneratedInteriorEliminationNode.fromInteriorIndex C i

def generatedInteriorEliminationDepth_fromNode
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {C : GeneratedInteriorEliminationCandidate Cell p A P wp W}
    (N : GeneratedInteriorEliminationNode Cell p A P wp W C) :
    GeneratedInteriorEliminationDepth Cell p A P wp W C N :=
  GeneratedInteriorEliminationDepth.fromNode N

def generatedInteriorEliminationMeasure_fromDepth
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {C : GeneratedInteriorEliminationCandidate Cell p A P wp W}
    {N : GeneratedInteriorEliminationNode Cell p A P wp W C}
    (D : GeneratedInteriorEliminationDepth Cell p A P wp W C N) :
    GeneratedInteriorEliminationMeasure Cell p A P wp W C N D :=
  GeneratedInteriorEliminationMeasure.fromDepth D

structure GeneratedInteriorEliminationCarrier
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) where
  startContract : SM3dbRPositiveFirstContract Cell p A P wp W E
  candidate : GeneratedInteriorEliminationCandidate Cell p A P wp W
  profileData : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  indexCarrier : Finset (GeneratedInteriorIndex A)
  nodeOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationNode Cell p A P wp W candidate
  depthOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationDepth Cell p A P wp W candidate (nodeOf i)
  measureOf :
    (i : GeneratedInteriorIndex A) →
      GeneratedInteriorEliminationMeasure Cell p A P wp W candidate
        (nodeOf i) (depthOf i)
  carrierStatus : SM3db1RCarrierStatus
  noFreeEliminationCarrierStatus : SM3db1RNoFreeEliminationCarrierStatus
  noExternalEliminationOrderOracleStatus :
    SM3db1RNoExternalEliminationOrderOracleStatus
  noFreePivotListStatus : SM3db1RNoFreePivotListStatus
  noInverseEntryFunctionStatus : SM3db1RNoInverseEntryFunctionStatus
  noMatrixExportStatus : SM3db1RNoMatrixExportStatus
  noEliminationTraceStatus : SM3db1RNoEliminationTraceStatus
  noTwoSidedInvStatus : SM3db1RNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus :
    SM3db1RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db1RNoInteriorEliminationDataStatus
  noMatrixInvStatus : SM3db1RNoMatrixInvStatus
  noDtnDataStatus : SM3db1RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db1RNoArithmeticTargetStatus
  nextPositivePhase : SM3db1RNextPositivePhase
  startContract_eq_main :
    startContract = sm3dbRPositiveFirstContract E
  candidate_eq_candidateEntry : candidate = E.candidate
  profileData_eq_candidateProfileData : profileData = candidate.profileData
  indexCarrier_eq_generatedInteriorIndex : indexCarrier = Finset.univ
  index_mem_carrier : ∀ i : GeneratedInteriorIndex A, i ∈ indexCarrier
  node_index_eq : ∀ i : GeneratedInteriorIndex A, (nodeOf i).index = i
  node_membership_from_partition :
    ∀ i : GeneratedInteriorIndex A, (nodeOf i).approximantIndex ∈ P.interiorCarrier
  node_profileData_eq :
    ∀ i : GeneratedInteriorIndex A, (nodeOf i).profileData = profileData
  node_candidate_eq :
    ∀ i : GeneratedInteriorIndex A, (nodeOf i).candidate = candidate
  depth_eq_index_level :
    ∀ i : GeneratedInteriorIndex A,
      (depthOf i).depth =
        (GeneratedInteriorIndex.level (nodeOf i).index).val
  measure_eq_cutoff_sub_depth :
    ∀ i : GeneratedInteriorIndex A,
      (measureOf i).measure = p.L_max - (depthOf i).depth
  startContract_nextPhase_eq :
    startContract.nextPositivePhase =
      SM3dbRNextPositivePhase.sm3db1RGeneratedInteriorEliminationCarrier
  carrierStatus_eq :
    carrierStatus = SM3db1RCarrierStatus.generatedInteriorEliminationCarrierClosed
  noFreeEliminationCarrierStatus_eq :
    noFreeEliminationCarrierStatus =
      SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier
  noExternalEliminationOrderOracleStatus_eq :
    noExternalEliminationOrderOracleStatus =
      SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle
  noFreePivotListStatus_eq :
    noFreePivotListStatus = SM3db1RNoFreePivotListStatus.noFreePivotList
  noInverseEntryFunctionStatus_eq :
    noInverseEntryFunctionStatus =
      SM3db1RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db1R
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db1RNoMatrixExportStatus.noMatrixExportInSM3db1R
  noEliminationTraceStatus_eq :
    noEliminationTraceStatus =
      SM3db1RNoEliminationTraceStatus.noEliminationTraceInSM3db1R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db1RNoTwoSidedInvStatus.noTwoSidedInvInSM3db1R
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3db1RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db1R
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db1RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db1R
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db1RNoMatrixInvStatus.noMatrixInvInSM3db1R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db1RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db1R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db1RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db1R
  nextPositivePhase_eq :
    nextPositivePhase =
      SM3db1RNextPositivePhase.sm3db2RGeneratedInteriorEliminationStep

namespace GeneratedInteriorEliminationCarrier

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}

def fromCandidateEntry
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    GeneratedInteriorEliminationCarrier Cell p A P wp W E where
  startContract := sm3dbRPositiveFirstContract E
  candidate := E.candidate
  profileData := E.candidate.profileData
  indexCarrier := Finset.univ
  nodeOf := fun i => generatedInteriorEliminationNode_fromIndex E.candidate i
  depthOf := fun i =>
    generatedInteriorEliminationDepth_fromNode
      (generatedInteriorEliminationNode_fromIndex E.candidate i)
  measureOf := fun i =>
    generatedInteriorEliminationMeasure_fromDepth
      (generatedInteriorEliminationDepth_fromNode
        (generatedInteriorEliminationNode_fromIndex E.candidate i))
  carrierStatus := SM3db1RCarrierStatus.generatedInteriorEliminationCarrierClosed
  noFreeEliminationCarrierStatus :=
    SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier
  noExternalEliminationOrderOracleStatus :=
    SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle
  noFreePivotListStatus := SM3db1RNoFreePivotListStatus.noFreePivotList
  noInverseEntryFunctionStatus :=
    SM3db1RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db1R
  noMatrixExportStatus := SM3db1RNoMatrixExportStatus.noMatrixExportInSM3db1R
  noEliminationTraceStatus :=
    SM3db1RNoEliminationTraceStatus.noEliminationTraceInSM3db1R
  noTwoSidedInvStatus := SM3db1RNoTwoSidedInvStatus.noTwoSidedInvInSM3db1R
  noInteriorEliminationCertificateStatus :=
    SM3db1RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db1R
  noInteriorEliminationDataStatus :=
    SM3db1RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db1R
  noMatrixInvStatus := SM3db1RNoMatrixInvStatus.noMatrixInvInSM3db1R
  noDtnDataStatus :=
    SM3db1RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db1R
  noArithmeticTargetStatus :=
    SM3db1RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db1R
  nextPositivePhase :=
    SM3db1RNextPositivePhase.sm3db2RGeneratedInteriorEliminationStep
  startContract_eq_main := by
    rfl
  candidate_eq_candidateEntry := by
    rfl
  profileData_eq_candidateProfileData := by
    rfl
  indexCarrier_eq_generatedInteriorIndex := by
    rfl
  index_mem_carrier := by
    intro i
    exact Finset.mem_univ i
  node_index_eq := by
    intro i
    rfl
  node_membership_from_partition := by
    intro i
    exact (generatedInteriorEliminationNode_fromIndex E.candidate i).interiorMembership
  node_profileData_eq := by
    intro i
    rfl
  node_candidate_eq := by
    intro i
    rfl
  depth_eq_index_level := by
    intro i
    rfl
  measure_eq_cutoff_sub_depth := by
    intro i
    rfl
  startContract_nextPhase_eq := by
    rfl
  carrierStatus_eq := by
    rfl
  noFreeEliminationCarrierStatus_eq := by
    rfl
  noExternalEliminationOrderOracleStatus_eq := by
    rfl
  noFreePivotListStatus_eq := by
    rfl
  noInverseEntryFunctionStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl
  noEliminationTraceStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPositivePhase_eq := by
    rfl

theorem noFreeEliminationCarrier
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noFreeEliminationCarrierStatus =
      SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier :=
  K.noFreeEliminationCarrierStatus_eq

theorem noExternalEliminationOrderOracle
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noExternalEliminationOrderOracleStatus =
      SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle :=
  K.noExternalEliminationOrderOracleStatus_eq

theorem noFreePivotList
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noFreePivotListStatus = SM3db1RNoFreePivotListStatus.noFreePivotList :=
  K.noFreePivotListStatus_eq

theorem noInverseEntryFunction
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noInverseEntryFunctionStatus =
      SM3db1RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db1R :=
  K.noInverseEntryFunctionStatus_eq

theorem noMatrixExport
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noMatrixExportStatus =
      SM3db1RNoMatrixExportStatus.noMatrixExportInSM3db1R :=
  K.noMatrixExportStatus_eq

theorem noEliminationTrace
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noEliminationTraceStatus =
      SM3db1RNoEliminationTraceStatus.noEliminationTraceInSM3db1R :=
  K.noEliminationTraceStatus_eq

theorem noTwoSidedInv
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noTwoSidedInvStatus =
      SM3db1RNoTwoSidedInvStatus.noTwoSidedInvInSM3db1R :=
  K.noTwoSidedInvStatus_eq

theorem noInteriorEliminationCertificate
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noInteriorEliminationCertificateStatus =
      SM3db1RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db1R :=
  K.noInteriorEliminationCertificateStatus_eq

theorem noInteriorEliminationData
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noInteriorEliminationDataStatus =
      SM3db1RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db1R :=
  K.noInteriorEliminationDataStatus_eq

theorem noMatrixInv
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noMatrixInvStatus = SM3db1RNoMatrixInvStatus.noMatrixInvInSM3db1R :=
  K.noMatrixInvStatus_eq

theorem noDtnData
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noDtnDataStatus =
      SM3db1RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db1R :=
  K.noDtnDataStatus_eq

theorem next_phase_is_step
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.nextPositivePhase =
      SM3db1RNextPositivePhase.sm3db2RGeneratedInteriorEliminationStep :=
  K.nextPositivePhase_eq

end GeneratedInteriorEliminationCarrier

def generatedInteriorEliminationCarrier_from_SM3cR_SM3dR
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    GeneratedInteriorEliminationCarrier Cell p A P wp W E :=
  GeneratedInteriorEliminationCarrier.fromCandidateEntry E

theorem noFreeEliminationCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noFreeEliminationCarrierStatus =
      SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier :=
  K.noFreeEliminationCarrierStatus_eq

theorem noExternalEliminationOrderOracle
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) :
    K.noExternalEliminationOrderOracleStatus =
      SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle :=
  K.noExternalEliminationOrderOracleStatus_eq

def regularGeneratedInteriorEliminationCarrier
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationCarrier
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp) :=
  generatedInteriorEliminationCarrier_from_SM3cR_SM3dR
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)

def variableGeneratedInteriorEliminationCarrier
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationCarrier
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp) :=
  generatedInteriorEliminationCarrier_from_SM3cR_SM3dR
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)

structure SM3db1RGeneratedInteriorEliminationCarrierLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3db1RGeneratedInteriorEliminationCarrierLedgerStatus
  sm3db0Ledger : SM3db0RPositiveFirstLedger b β p regularWeight variableWeight
  regularCarrier :
    GeneratedInteriorEliminationCarrier
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
  variableCarrier :
    GeneratedInteriorEliminationCarrier
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
  sm3db0Ledger_eq_main :
    sm3db0Ledger = sm3db0RPositiveFirstLedger b β p regularWeight variableWeight
  regularCarrier_eq_main :
    regularCarrier = regularGeneratedInteriorEliminationCarrier b p regularWeight
  variableCarrier_eq_main :
    variableCarrier = variableGeneratedInteriorEliminationCarrier β p variableWeight
  regularNoFreeCarrier :
    regularCarrier.noFreeEliminationCarrierStatus =
      SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier
  variableNoFreeCarrier :
    variableCarrier.noFreeEliminationCarrierStatus =
      SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier
  regularNoExternalOrderOracle :
    regularCarrier.noExternalEliminationOrderOracleStatus =
      SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle
  variableNoExternalOrderOracle :
    variableCarrier.noExternalEliminationOrderOracleStatus =
      SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle
  regularNoInverseEntryFunction :
    regularCarrier.noInverseEntryFunctionStatus =
      SM3db1RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db1R
  variableNoInverseEntryFunction :
    variableCarrier.noInverseEntryFunctionStatus =
      SM3db1RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db1R
  regularNoMatrixExport :
    regularCarrier.noMatrixExportStatus =
      SM3db1RNoMatrixExportStatus.noMatrixExportInSM3db1R
  variableNoMatrixExport :
    variableCarrier.noMatrixExportStatus =
      SM3db1RNoMatrixExportStatus.noMatrixExportInSM3db1R
  regularNoEliminationTrace :
    regularCarrier.noEliminationTraceStatus =
      SM3db1RNoEliminationTraceStatus.noEliminationTraceInSM3db1R
  variableNoEliminationTrace :
    variableCarrier.noEliminationTraceStatus =
      SM3db1RNoEliminationTraceStatus.noEliminationTraceInSM3db1R
  regularNextPositivePhase :
    regularCarrier.nextPositivePhase =
      SM3db1RNextPositivePhase.sm3db2RGeneratedInteriorEliminationStep
  variableNextPositivePhase :
    variableCarrier.nextPositivePhase =
      SM3db1RNextPositivePhase.sm3db2RGeneratedInteriorEliminationStep
  status_eq_closed :
    status =
      SM3db1RGeneratedInteriorEliminationCarrierLedgerStatus.generatedInteriorEliminationCarrierClosed

def sm3db1RGeneratedInteriorEliminationCarrierLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight where
  status :=
    SM3db1RGeneratedInteriorEliminationCarrierLedgerStatus.generatedInteriorEliminationCarrierClosed
  sm3db0Ledger := sm3db0RPositiveFirstLedger b β p regularWeight variableWeight
  regularCarrier := regularGeneratedInteriorEliminationCarrier b p regularWeight
  variableCarrier := variableGeneratedInteriorEliminationCarrier β p variableWeight
  sm3db0Ledger_eq_main := by
    rfl
  regularCarrier_eq_main := by
    rfl
  variableCarrier_eq_main := by
    rfl
  regularNoFreeCarrier := by
    rfl
  variableNoFreeCarrier := by
    rfl
  regularNoExternalOrderOracle := by
    rfl
  variableNoExternalOrderOracle := by
    rfl
  regularNoInverseEntryFunction := by
    rfl
  variableNoInverseEntryFunction := by
    rfl
  regularNoMatrixExport := by
    rfl
  variableNoMatrixExport := by
    rfl
  regularNoEliminationTrace := by
    rfl
  variableNoEliminationTrace := by
    rfl
  regularNextPositivePhase := by
    rfl
  variableNextPositivePhase := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3db1RGeneratedInteriorEliminationCarrierLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight).status =
      SM3db1RGeneratedInteriorEliminationCarrierLedgerStatus.generatedInteriorEliminationCarrierClosed := by
  rfl

theorem sm3db1RGeneratedInteriorEliminationCarrierLedger_regularNoFreeCarrier
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight).regularCarrier.noFreeEliminationCarrierStatus =
      SM3db1RNoFreeEliminationCarrierStatus.noFreeEliminationCarrier := by
  rfl

theorem sm3db1RGeneratedInteriorEliminationCarrierLedger_variableNoExternalOrderOracle
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight).variableCarrier.noExternalEliminationOrderOracleStatus =
      SM3db1RNoExternalEliminationOrderOracleStatus.noExternalEliminationOrderOracle := by
  rfl

theorem sm3db1RGeneratedInteriorEliminationCarrierLedger_regularNoInverseEntryFunction
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight).regularCarrier.noInverseEntryFunctionStatus =
      SM3db1RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db1R := by
  rfl

theorem sm3db1RGeneratedInteriorEliminationCarrierLedger_variableNoMatrixExport
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight).variableCarrier.noMatrixExportStatus =
      SM3db1RNoMatrixExportStatus.noMatrixExportInSM3db1R := by
  rfl

theorem sm3db1RGeneratedInteriorEliminationCarrierLedger_regularNextPositivePhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight).regularCarrier.nextPositivePhase =
      SM3db1RNextPositivePhase.sm3db2RGeneratedInteriorEliminationStep := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
