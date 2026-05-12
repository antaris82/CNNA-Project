import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2RPivotDatumStatus where
  | pivotFromSM3db1RCarrierNode
  deriving DecidableEq, Repr

inductive SM3db2RResidualDatumStatus where
  | residualFromSM3cRSM3dRProfile
  deriving DecidableEq, Repr

inductive SM3db2RStepUpdateStatus where
  | stepUpdateFromSM3cRSM3dRCandidate
  deriving DecidableEq, Repr

inductive SM3db2REliminationStepStatus where
  | generatedInteriorEliminationLocalStepClosed
  deriving DecidableEq, Repr

inductive SM3db2RNoMatrixInvStatus where
  | noMatrixInvForEliminationStep
  deriving DecidableEq, Repr

inductive SM3db2RNoGlobalInverseStatus where
  | noGlobalInverseForEliminationStep
  deriving DecidableEq, Repr

inductive SM3db2RNoCertificateStatus where
  | noCertificateForEliminationStep
  deriving DecidableEq, Repr

inductive SM3db2RNoFreePivotDataStatus where
  | noFreePivotData
  deriving DecidableEq, Repr

inductive SM3db2RNoGlobalPivotOrderStatus where
  | noGlobalPivotOrder
  deriving DecidableEq, Repr

inductive SM3db2RNoTraceSemanticsStatus where
  | noTraceSemantics
  deriving DecidableEq, Repr

inductive SM3db2RNoInverseEntryFunctionStatus where
  | noInverseEntryFunctionInSM3db2R
  deriving DecidableEq, Repr

inductive SM3db2RNoMatrixExportStatus where
  | noMatrixExportInSM3db2R
  deriving DecidableEq, Repr

inductive SM3db2RNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db2R
  deriving DecidableEq, Repr

inductive SM3db2RNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2R
  deriving DecidableEq, Repr

inductive SM3db2RNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2R
  deriving DecidableEq, Repr

inductive SM3db2RNextPositivePhase where
  | sm3db3RGeneratedInteriorEliminationTrace
  deriving DecidableEq, Repr

inductive SM3db2RGeneratedInteriorEliminationStepLedgerStatus where
  | generatedInteriorEliminationLocalStepClosed
  deriving DecidableEq, Repr

def generatedInteriorLocalBaseEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorBlock W i j

def generatedInteriorLocalRowResidual
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (pivot j : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorBlock W pivot j

def generatedInteriorLocalColumnResidual
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (pivot i : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorBlock W i pivot

def generatedInteriorLocalPivotEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (pivot : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorBlock W pivot pivot

structure GeneratedInteriorPivotDatum
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) where
  pivotIndex : GeneratedInteriorIndex A
  node : GeneratedInteriorEliminationNode Cell p A P wp W K.candidate
  depth : Nat
  measure : Nat
  pivotEntry : ℝ
  pivotDatumStatus : SM3db2RPivotDatumStatus
  noFreePivotDataStatus : SM3db2RNoFreePivotDataStatus
  noGlobalPivotOrderStatus : SM3db2RNoGlobalPivotOrderStatus
  node_eq_carrierNode : node = K.nodeOf pivotIndex
  node_index_eq_pivot : node.index = pivotIndex
  node_membership_from_partition : node.approximantIndex ∈ P.interiorCarrier
  node_profileData_eq_carrierProfileData : node.profileData = K.profileData
  node_candidate_eq_carrierCandidate : node.candidate = K.candidate
  depth_eq_carrierDepth : depth = (K.depthOf pivotIndex).depth
  measure_eq_carrierMeasure : measure = (K.measureOf pivotIndex).measure
  pivotEntry_eq_interiorBlock : pivotEntry = generatedInteriorLocalPivotEntry W pivotIndex
  pivotDatumStatus_eq :
    pivotDatumStatus = SM3db2RPivotDatumStatus.pivotFromSM3db1RCarrierNode
  noFreePivotDataStatus_eq :
    noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData
  noGlobalPivotOrderStatus_eq :
    noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder

namespace GeneratedInteriorPivotDatum

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

def fromCarrierNode
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorPivotDatum Cell p A P wp W E K where
  pivotIndex := i
  node := K.nodeOf i
  depth := (K.depthOf i).depth
  measure := (K.measureOf i).measure
  pivotEntry := generatedInteriorLocalPivotEntry W i
  pivotDatumStatus := SM3db2RPivotDatumStatus.pivotFromSM3db1RCarrierNode
  noFreePivotDataStatus := SM3db2RNoFreePivotDataStatus.noFreePivotData
  noGlobalPivotOrderStatus := SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder
  node_eq_carrierNode := by
    rfl
  node_index_eq_pivot :=
    K.node_index_eq i
  node_membership_from_partition :=
    K.node_membership_from_partition i
  node_profileData_eq_carrierProfileData :=
    K.node_profileData_eq i
  node_candidate_eq_carrierCandidate :=
    K.node_candidate_eq i
  depth_eq_carrierDepth := by
    rfl
  measure_eq_carrierMeasure := by
    rfl
  pivotEntry_eq_interiorBlock := by
    rfl
  pivotDatumStatus_eq := by
    rfl
  noFreePivotDataStatus_eq := by
    rfl
  noGlobalPivotOrderStatus_eq := by
    rfl

theorem pivot_bound_to_SM3db1R_node
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K) :
    Q.node = K.nodeOf Q.pivotIndex :=
  Q.node_eq_carrierNode

theorem noFreePivotData
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K) :
    Q.noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData :=
  Q.noFreePivotDataStatus_eq

theorem noGlobalPivotOrder
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K) :
    Q.noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder :=
  Q.noGlobalPivotOrderStatus_eq

end GeneratedInteriorPivotDatum

structure GeneratedInteriorResidualDatum
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
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K) where
  profileData : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  candidate : GeneratedInteriorEliminationCandidate Cell p A P wp W
  rowResidual : GeneratedInteriorIndex A → ℝ
  columnResidual : GeneratedInteriorIndex A → ℝ
  residualDatumStatus : SM3db2RResidualDatumStatus
  profileSourceStatus : SM3db1RProfileSourceStatus
  candidateSourceStatus : SM3db1RCandidateSourceStatus
  profileData_eq_carrierProfileData : profileData = K.profileData
  candidate_eq_carrierCandidate : candidate = K.candidate
  candidate_profile_eq_profileData : candidate.profile = profileData.profile
  candidate_sourceCompatible :
    GeneratedInteriorEliminationCandidateSourceCompatible candidate.source profileData.profile
  rowResidual_eq_interiorBlock :
    ∀ j : GeneratedInteriorIndex A,
      rowResidual j = generatedInteriorLocalRowResidual W Q.pivotIndex j
  columnResidual_eq_interiorBlock :
    ∀ i : GeneratedInteriorIndex A,
      columnResidual i = generatedInteriorLocalColumnResidual W Q.pivotIndex i
  residualDatumStatus_eq :
    residualDatumStatus = SM3db2RResidualDatumStatus.residualFromSM3cRSM3dRProfile
  profileSourceStatus_eq :
    profileSourceStatus =
      SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure
  candidateSourceStatus_eq :
    candidateSourceStatus =
      SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate

namespace GeneratedInteriorResidualDatum

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
variable {Q : GeneratedInteriorPivotDatum Cell p A P wp W E K}

def fromSM3cRSM3dRProfile
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K) :
    GeneratedInteriorResidualDatum Cell p A P wp W E K Q where
  profileData := K.candidate.profileData
  candidate := K.candidate
  rowResidual := fun j => generatedInteriorLocalRowResidual W Q.pivotIndex j
  columnResidual := fun i => generatedInteriorLocalColumnResidual W Q.pivotIndex i
  residualDatumStatus := SM3db2RResidualDatumStatus.residualFromSM3cRSM3dRProfile
  profileSourceStatus :=
    SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure
  candidateSourceStatus :=
    SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate
  profileData_eq_carrierProfileData :=
    K.profileData_eq_candidateProfileData.symm
  candidate_eq_carrierCandidate := by
    rfl
  candidate_profile_eq_profileData :=
    K.candidate.profile_eq_SM3cR_profile
  candidate_sourceCompatible :=
    K.candidate.sourceCompatible
  rowResidual_eq_interiorBlock := by
    intro j
    rfl
  columnResidual_eq_interiorBlock := by
    intro i
    rfl
  residualDatumStatus_eq := by
    rfl
  profileSourceStatus_eq := by
    rfl
  candidateSourceStatus_eq := by
    rfl

theorem residual_uses_SM3cR_SM3dR
    (R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q) :
    R.profileSourceStatus =
        SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure ∧
      R.candidateSourceStatus =
        SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate :=
  And.intro R.profileSourceStatus_eq R.candidateSourceStatus_eq

theorem rowResidual_eq
    (R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q)
    (j : GeneratedInteriorIndex A) :
    R.rowResidual j = generatedInteriorLocalRowResidual W Q.pivotIndex j :=
  R.rowResidual_eq_interiorBlock j

theorem columnResidual_eq
    (R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q)
    (i : GeneratedInteriorIndex A) :
    R.columnResidual i = generatedInteriorLocalColumnResidual W Q.pivotIndex i :=
  R.columnResidual_eq_interiorBlock i

end GeneratedInteriorResidualDatum

structure GeneratedInteriorStepUpdate
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
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K)
    (R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q) where
  pivotDatum : GeneratedInteriorPivotDatum Cell p A P wp W E K
  residualDatum : GeneratedInteriorResidualDatum Cell p A P wp W E K Q
  candidate : GeneratedInteriorEliminationCandidate Cell p A P wp W
  baseEntry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  rowResidual : GeneratedInteriorIndex A → ℝ
  columnResidual : GeneratedInteriorIndex A → ℝ
  pivotEntry : ℝ
  stepUpdateStatus : SM3db2RStepUpdateStatus
  noMatrixInvStatus : SM3db2RNoMatrixInvStatus
  noGlobalInverseStatus : SM3db2RNoGlobalInverseStatus
  noCertificateStatus : SM3db2RNoCertificateStatus
  noInverseEntryFunctionStatus : SM3db2RNoInverseEntryFunctionStatus
  noMatrixExportStatus : SM3db2RNoMatrixExportStatus
  pivotDatum_eq : pivotDatum = Q
  residualDatum_eq : residualDatum = R
  candidate_eq_residualCandidate : candidate = R.candidate
  baseEntry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      baseEntry i j = generatedInteriorLocalBaseEntry W i j
  rowResidual_eq_residualDatum :
    ∀ j : GeneratedInteriorIndex A, rowResidual j = R.rowResidual j
  columnResidual_eq_residualDatum :
    ∀ i : GeneratedInteriorIndex A, columnResidual i = R.columnResidual i
  pivotEntry_eq_pivotDatum : pivotEntry = Q.pivotEntry
  stepUpdateStatus_eq :
    stepUpdateStatus = SM3db2RStepUpdateStatus.stepUpdateFromSM3cRSM3dRCandidate
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  noGlobalInverseStatus_eq :
    noGlobalInverseStatus = SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep
  noCertificateStatus_eq :
    noCertificateStatus = SM3db2RNoCertificateStatus.noCertificateForEliminationStep
  noInverseEntryFunctionStatus_eq :
    noInverseEntryFunctionStatus =
      SM3db2RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db2R
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db2RNoMatrixExportStatus.noMatrixExportInSM3db2R

namespace GeneratedInteriorStepUpdate

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
variable {Q : GeneratedInteriorPivotDatum Cell p A P wp W E K}
variable {R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q}

def fromSM3cRSM3dRCandidate
    (R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q) :
    GeneratedInteriorStepUpdate Cell p A P wp W E K Q R where
  pivotDatum := Q
  residualDatum := R
  candidate := R.candidate
  baseEntry := fun i j => generatedInteriorLocalBaseEntry W i j
  rowResidual := R.rowResidual
  columnResidual := R.columnResidual
  pivotEntry := Q.pivotEntry
  stepUpdateStatus := SM3db2RStepUpdateStatus.stepUpdateFromSM3cRSM3dRCandidate
  noMatrixInvStatus := SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  noGlobalInverseStatus := SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep
  noCertificateStatus := SM3db2RNoCertificateStatus.noCertificateForEliminationStep
  noInverseEntryFunctionStatus :=
    SM3db2RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db2R
  noMatrixExportStatus := SM3db2RNoMatrixExportStatus.noMatrixExportInSM3db2R
  pivotDatum_eq := by
    rfl
  residualDatum_eq := by
    rfl
  candidate_eq_residualCandidate := by
    rfl
  baseEntry_eq_interiorBlock := by
    intro i j
    rfl
  rowResidual_eq_residualDatum := by
    intro j
    rfl
  columnResidual_eq_residualDatum := by
    intro i
    rfl
  pivotEntry_eq_pivotDatum := by
    rfl
  stepUpdateStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noGlobalInverseStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noInverseEntryFunctionStatus_eq := by
    rfl
  noMatrixExportStatus_eq := by
    rfl

theorem noMatrixInv
    (U : GeneratedInteriorStepUpdate Cell p A P wp W E K Q R) :
    U.noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep :=
  U.noMatrixInvStatus_eq

theorem noGlobalInverse
    (U : GeneratedInteriorStepUpdate Cell p A P wp W E K Q R) :
    U.noGlobalInverseStatus =
      SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep :=
  U.noGlobalInverseStatus_eq

theorem noCertificate
    (U : GeneratedInteriorStepUpdate Cell p A P wp W E K Q R) :
    U.noCertificateStatus = SM3db2RNoCertificateStatus.noCertificateForEliminationStep :=
  U.noCertificateStatus_eq

end GeneratedInteriorStepUpdate

structure GeneratedInteriorEliminationStep
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E) where
  pivotDatum : GeneratedInteriorPivotDatum Cell p A P wp W E K
  residualDatum : GeneratedInteriorResidualDatum Cell p A P wp W E K pivotDatum
  stepUpdate :
    GeneratedInteriorStepUpdate Cell p A P wp W E K pivotDatum residualDatum
  profileData : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  candidate : GeneratedInteriorEliminationCandidate Cell p A P wp W
  stepStatus : SM3db2REliminationStepStatus
  noMatrixInvStatus : SM3db2RNoMatrixInvStatus
  noFreePivotDataStatus : SM3db2RNoFreePivotDataStatus
  noGlobalPivotOrderStatus : SM3db2RNoGlobalPivotOrderStatus
  noTraceSemanticsStatus : SM3db2RNoTraceSemanticsStatus
  noGlobalInverseStatus : SM3db2RNoGlobalInverseStatus
  noCertificateStatus : SM3db2RNoCertificateStatus
  noInverseEntryFunctionStatus : SM3db2RNoInverseEntryFunctionStatus
  noMatrixExportStatus : SM3db2RNoMatrixExportStatus
  noTwoSidedInvStatus : SM3db2RNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2RNoArithmeticTargetStatus
  nextPositivePhase : SM3db2RNextPositivePhase
  profileData_eq_carrierProfileData : profileData = K.profileData
  candidate_eq_carrierCandidate : candidate = K.candidate
  pivot_from_carrierNode : pivotDatum.node = K.nodeOf pivotDatum.pivotIndex
  residual_from_profile :
    residualDatum.residualDatumStatus =
      SM3db2RResidualDatumStatus.residualFromSM3cRSM3dRProfile
  update_from_candidate :
    stepUpdate.stepUpdateStatus =
      SM3db2RStepUpdateStatus.stepUpdateFromSM3cRSM3dRCandidate
  stepStatus_eq :
    stepStatus = SM3db2REliminationStepStatus.generatedInteriorEliminationLocalStepClosed
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  noFreePivotDataStatus_eq :
    noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData
  noGlobalPivotOrderStatus_eq :
    noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder
  noTraceSemanticsStatus_eq :
    noTraceSemanticsStatus = SM3db2RNoTraceSemanticsStatus.noTraceSemantics
  noGlobalInverseStatus_eq :
    noGlobalInverseStatus = SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep
  noCertificateStatus_eq :
    noCertificateStatus = SM3db2RNoCertificateStatus.noCertificateForEliminationStep
  noInverseEntryFunctionStatus_eq :
    noInverseEntryFunctionStatus =
      SM3db2RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db2R
  noMatrixExportStatus_eq :
    noMatrixExportStatus = SM3db2RNoMatrixExportStatus.noMatrixExportInSM3db2R
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2RNoTwoSidedInvStatus.noTwoSidedInvInSM3db2R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db2RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2R
  nextPositivePhase_eq :
    nextPositivePhase = SM3db2RNextPositivePhase.sm3db3RGeneratedInteriorEliminationTrace

namespace GeneratedInteriorEliminationStep

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

def fromCarrierNode
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorEliminationStep Cell p A P wp W E K :=
  let Q : GeneratedInteriorPivotDatum Cell p A P wp W E K :=
    GeneratedInteriorPivotDatum.fromCarrierNode K i
  let R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q :=
    GeneratedInteriorResidualDatum.fromSM3cRSM3dRProfile Q
  let U : GeneratedInteriorStepUpdate Cell p A P wp W E K Q R :=
    GeneratedInteriorStepUpdate.fromSM3cRSM3dRCandidate R
  {
    pivotDatum := Q
    residualDatum := R
    stepUpdate := U
    profileData := K.profileData
    candidate := K.candidate
    stepStatus := SM3db2REliminationStepStatus.generatedInteriorEliminationLocalStepClosed
    noMatrixInvStatus := SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
    noFreePivotDataStatus := SM3db2RNoFreePivotDataStatus.noFreePivotData
    noGlobalPivotOrderStatus := SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder
    noTraceSemanticsStatus := SM3db2RNoTraceSemanticsStatus.noTraceSemantics
    noGlobalInverseStatus := SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep
    noCertificateStatus := SM3db2RNoCertificateStatus.noCertificateForEliminationStep
    noInverseEntryFunctionStatus :=
      SM3db2RNoInverseEntryFunctionStatus.noInverseEntryFunctionInSM3db2R
    noMatrixExportStatus := SM3db2RNoMatrixExportStatus.noMatrixExportInSM3db2R
    noTwoSidedInvStatus := SM3db2RNoTwoSidedInvStatus.noTwoSidedInvInSM3db2R
    noDtnDataStatus :=
      SM3db2RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2R
    noArithmeticTargetStatus :=
      SM3db2RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2R
    nextPositivePhase := SM3db2RNextPositivePhase.sm3db3RGeneratedInteriorEliminationTrace
    profileData_eq_carrierProfileData := by
      rfl
    candidate_eq_carrierCandidate := by
      rfl
    pivot_from_carrierNode := by
      rfl
    residual_from_profile := by
      rfl
    update_from_candidate := by
      rfl
    stepStatus_eq := by
      rfl
    noMatrixInvStatus_eq := by
      rfl
    noFreePivotDataStatus_eq := by
      rfl
    noGlobalPivotOrderStatus_eq := by
      rfl
    noTraceSemanticsStatus_eq := by
      rfl
    noGlobalInverseStatus_eq := by
      rfl
    noCertificateStatus_eq := by
      rfl
    noInverseEntryFunctionStatus_eq := by
      rfl
    noMatrixExportStatus_eq := by
      rfl
    noTwoSidedInvStatus_eq := by
      rfl
    noDtnDataStatus_eq := by
      rfl
    noArithmeticTargetStatus_eq := by
      rfl
    nextPositivePhase_eq := by
      rfl
  }

theorem uses_only_SM3cR_SM3dR
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.residualDatum.profileSourceStatus =
        SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure ∧
      S.residualDatum.candidateSourceStatus =
        SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate ∧
      S.stepUpdate.stepUpdateStatus =
        SM3db2RStepUpdateStatus.stepUpdateFromSM3cRSM3dRCandidate :=
  And.intro S.residualDatum.profileSourceStatus_eq
    (And.intro S.residualDatum.candidateSourceStatus_eq S.stepUpdate.stepUpdateStatus_eq)

theorem noMatrixInv
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep :=
  S.noMatrixInvStatus_eq

theorem noFreePivotData
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData :=
  S.noFreePivotDataStatus_eq

theorem noGlobalPivotOrder
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder :=
  S.noGlobalPivotOrderStatus_eq

theorem noTraceSemantics
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noTraceSemanticsStatus = SM3db2RNoTraceSemanticsStatus.noTraceSemantics :=
  S.noTraceSemanticsStatus_eq

end GeneratedInteriorEliminationStep

def generatedInteriorPivotDatum_from_SM3db1R_node
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorPivotDatum Cell p A P wp W E K :=
  GeneratedInteriorPivotDatum.fromCarrierNode K i

def residualDatum_from_SM3cR_SM3dR_profile
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
    (Q : GeneratedInteriorPivotDatum Cell p A P wp W E K) :
    GeneratedInteriorResidualDatum Cell p A P wp W E K Q :=
  GeneratedInteriorResidualDatum.fromSM3cRSM3dRProfile Q

def stepUpdate_from_SM3cR_SM3dR_candidate
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
    {Q : GeneratedInteriorPivotDatum Cell p A P wp W E K}
    (R : GeneratedInteriorResidualDatum Cell p A P wp W E K Q) :
    GeneratedInteriorStepUpdate Cell p A P wp W E K Q R :=
  GeneratedInteriorStepUpdate.fromSM3cRSM3dRCandidate R

def localStep_from_SM3db1R_node
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorEliminationStep Cell p A P wp W E K :=
  GeneratedInteriorEliminationStep.fromCarrierNode K i

def generatedInteriorEliminationStep_from_profile
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorEliminationStep Cell p A P wp W E K :=
  localStep_from_SM3db1R_node K i

theorem generatedInteriorStep_uses_only_SM3cR_SM3dR
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.residualDatum.profileSourceStatus =
        SM3db1RProfileSourceStatus.profileFromSM3cRInteriorBlockStructure ∧
      S.residualDatum.candidateSourceStatus =
        SM3db1RCandidateSourceStatus.candidateFromSM3dRStructureDependentCandidate ∧
      S.stepUpdate.stepUpdateStatus =
        SM3db2RStepUpdateStatus.stepUpdateFromSM3cRSM3dRCandidate :=
  GeneratedInteriorEliminationStep.uses_only_SM3cR_SM3dR S

theorem noMatrixInv_for_eliminationStep
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep :=
  S.noMatrixInvStatus_eq

theorem noFreePivotData
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData :=
  S.noFreePivotDataStatus_eq

theorem noGlobalPivotOrder_for_eliminationStep
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder :=
  S.noGlobalPivotOrderStatus_eq

theorem noTraceSemantics_for_eliminationStep
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) :
    S.noTraceSemanticsStatus = SM3db2RNoTraceSemanticsStatus.noTraceSemantics :=
  S.noTraceSemanticsStatus_eq

def regularGeneratedInteriorEliminationStep
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (i : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p)) :
    GeneratedInteriorEliminationStep
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp) :=
  generatedInteriorEliminationStep_from_profile
    (regularGeneratedInteriorEliminationCarrier b p wp) i

def variableGeneratedInteriorEliminationStep
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (i : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    GeneratedInteriorEliminationStep
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp) :=
  generatedInteriorEliminationStep_from_profile
    (variableGeneratedInteriorEliminationCarrier β p wp) i

structure SM3db2RGeneratedInteriorEliminationStepLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3db2RGeneratedInteriorEliminationStepLedgerStatus
  sm3db1Ledger : SM3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight
  regularStep :
    GeneratedInteriorEliminationStep
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
  variableStep :
    GeneratedInteriorEliminationStep
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
  sm3db1Ledger_eq_main :
    sm3db1Ledger = sm3db1RGeneratedInteriorEliminationCarrierLedger
      b β p regularWeight variableWeight
  regularStep_eq_main :
    regularStep = regularGeneratedInteriorEliminationStep b p regularWeight regularPivot
  variableStep_eq_main :
    variableStep = variableGeneratedInteriorEliminationStep β p variableWeight variablePivot
  regularNoMatrixInv :
    regularStep.noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  variableNoMatrixInv :
    variableStep.noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  regularNoFreePivotData :
    regularStep.noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData
  variableNoFreePivotData :
    variableStep.noFreePivotDataStatus = SM3db2RNoFreePivotDataStatus.noFreePivotData
  regularNoGlobalPivotOrder :
    regularStep.noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder
  variableNoGlobalPivotOrder :
    variableStep.noGlobalPivotOrderStatus = SM3db2RNoGlobalPivotOrderStatus.noGlobalPivotOrder
  regularNoTraceSemantics :
    regularStep.noTraceSemanticsStatus = SM3db2RNoTraceSemanticsStatus.noTraceSemantics
  variableNoTraceSemantics :
    variableStep.noTraceSemanticsStatus = SM3db2RNoTraceSemanticsStatus.noTraceSemantics
  regularNextPositivePhase :
    regularStep.nextPositivePhase = SM3db2RNextPositivePhase.sm3db3RGeneratedInteriorEliminationTrace
  variableNextPositivePhase :
    variableStep.nextPositivePhase = SM3db2RNextPositivePhase.sm3db3RGeneratedInteriorEliminationTrace
  status_eq_closed :
    status = SM3db2RGeneratedInteriorEliminationStepLedgerStatus.generatedInteriorEliminationLocalStepClosed

def sm3db2RGeneratedInteriorEliminationStepLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3db2RGeneratedInteriorEliminationStepLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status := SM3db2RGeneratedInteriorEliminationStepLedgerStatus.generatedInteriorEliminationLocalStepClosed
  sm3db1Ledger := sm3db1RGeneratedInteriorEliminationCarrierLedger b β p regularWeight variableWeight
  regularStep := regularGeneratedInteriorEliminationStep b p regularWeight regularPivot
  variableStep := variableGeneratedInteriorEliminationStep β p variableWeight variablePivot
  sm3db1Ledger_eq_main := by
    rfl
  regularStep_eq_main := by
    rfl
  variableStep_eq_main := by
    rfl
  regularNoMatrixInv := by
    rfl
  variableNoMatrixInv := by
    rfl
  regularNoFreePivotData := by
    rfl
  variableNoFreePivotData := by
    rfl
  regularNoGlobalPivotOrder := by
    rfl
  variableNoGlobalPivotOrder := by
    rfl
  regularNoTraceSemantics := by
    rfl
  variableNoTraceSemantics := by
    rfl
  regularNextPositivePhase := by
    rfl
  variableNextPositivePhase := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3db2RGeneratedInteriorEliminationStepLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db2RGeneratedInteriorEliminationStepLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3db2RGeneratedInteriorEliminationStepLedgerStatus.generatedInteriorEliminationLocalStepClosed := by
  rfl

theorem sm3db2RGeneratedInteriorEliminationStepLedger_regularNoFreePivotData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db2RGeneratedInteriorEliminationStepLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularStep.noFreePivotDataStatus =
      SM3db2RNoFreePivotDataStatus.noFreePivotData := by
  rfl

theorem sm3db2RGeneratedInteriorEliminationStepLedger_variableNoTraceSemantics
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db2RGeneratedInteriorEliminationStepLedger
      b β p regularWeight variableWeight regularPivot variablePivot).variableStep.noTraceSemanticsStatus =
      SM3db2RNoTraceSemanticsStatus.noTraceSemantics := by
  rfl

theorem sm3db2RGeneratedInteriorEliminationStepLedger_regularNextPositivePhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3db2RGeneratedInteriorEliminationStepLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularStep.nextPositivePhase =
      SM3db2RNextPositivePhase.sm3db3RGeneratedInteriorEliminationTrace := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
