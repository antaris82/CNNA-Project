import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2bRPivotNonzeroSourceStatus where
  | pivotEntryNonzeroMustComeFromGeneratedDegreeProfile
  deriving DecidableEq, Repr

inductive SM3db2bRPerPivotRegularityStatus where
  | perPivotRegularityFromTracePivotScaleWitness
  deriving DecidableEq, Repr

inductive SM3db2bRTraceRegularityStatus where
  | traceRegularityFromPerPivotScaleWitness
  deriving DecidableEq, Repr

inductive SM3db2bRPivotScaleSourceStatus where
  | pivotScaleWitnessMustComeFromGeneratedDegreeProfile
  deriving DecidableEq, Repr

inductive SM3db2bRNoMatrixInvStatus where
  | noMatrixInvInPerPivotRegularity
  deriving DecidableEq, Repr

inductive SM3db2bRNoTwoSidedInvStatus where
  | noTwoSidedInvInPerPivotRegularity
  deriving DecidableEq, Repr

inductive SM3db2bRNoProductIdentityProofStatus where
  | noProductIdentityProofInPerPivotRegularity
  deriving DecidableEq, Repr

inductive SM3db2bRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2bR
  deriving DecidableEq, Repr

inductive SM3db2bRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2bR
  deriving DecidableEq, Repr

inductive SM3db2bRNextPhaseStatus where
  | sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  | sm3db2cRTracePivotEntryNonzeroFromGeneratedDegree
  | sm3db2cRTracePivotScaleWitnessFromGeneratedDegree
  deriving DecidableEq, Repr

structure GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR
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
  sourceAudit : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T
  pivotNonzeroSourceStatus : SM3db2bRPivotNonzeroSourceStatus
  noMatrixInvStatus : SM3db2bRNoMatrixInvStatus
  noTwoSidedInvStatus : SM3db2bRNoTwoSidedInvStatus
  noProductIdentityProofStatus : SM3db2bRNoProductIdentityProofStatus
  noDtnDataStatus : SM3db2bRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2bRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2bRNextPhaseStatus
  pivotEntry_eq_block :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedInteriorBlock W
          (T.localStepOf pivot).pivotDatum.pivotIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex
  pivotEntry_eq_dirichletDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  pivotNonzeroSourceStatus_eq :
    pivotNonzeroSourceStatus =
      SM3db2bRPivotNonzeroSourceStatus.pivotEntryNonzeroMustComeFromGeneratedDegreeProfile
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2bRNoMatrixInvStatus.noMatrixInvInPerPivotRegularity
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2bRNoTwoSidedInvStatus.noTwoSidedInvInPerPivotRegularity
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2bRNoProductIdentityProofStatus.noProductIdentityProofInPerPivotRegularity
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2bRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2bR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2bRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2bR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2bRNextPhaseStatus.sm3db2cRTracePivotScaleWitnessFromGeneratedDegree

namespace GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR

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

def fromSourceAudit
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T) :
    GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR Cell p A P wp W E K T where
  sourceAudit := A0
  pivotNonzeroSourceStatus :=
    SM3db2bRPivotNonzeroSourceStatus.pivotEntryNonzeroMustComeFromGeneratedDegreeProfile
  noMatrixInvStatus := SM3db2bRNoMatrixInvStatus.noMatrixInvInPerPivotRegularity
  noTwoSidedInvStatus := SM3db2bRNoTwoSidedInvStatus.noTwoSidedInvInPerPivotRegularity
  noProductIdentityProofStatus :=
    SM3db2bRNoProductIdentityProofStatus.noProductIdentityProofInPerPivotRegularity
  noDtnDataStatus := SM3db2bRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2bR
  noArithmeticTargetStatus :=
    SM3db2bRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2bR
  nextPhaseStatus := SM3db2bRNextPhaseStatus.sm3db2cRTracePivotScaleWitnessFromGeneratedDegree
  pivotEntry_eq_block := by
    intro pivot
    exact A0.has_pivotEntry_eq_block pivot
  pivotEntry_eq_dirichletDegree := by
    intro pivot
    calc
      (T.localStepOf pivot).stepUpdate.pivotEntry =
          generatedInteriorBlock W
            (T.localStepOf pivot).pivotDatum.pivotIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex :=
        A0.has_pivotEntry_eq_block pivot
      _ = generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) :=
        generatedInteriorBlock_diag_degree_or_regularized_degree W
          (T.localStepOf pivot).pivotDatum.pivotIndex
  pivotNonzeroSourceStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem nextPhase_is_tracePivotScaleWitness
    (R : GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR Cell p A P wp W E K T) :
    R.nextPhaseStatus = SM3db2bRNextPhaseStatus.sm3db2cRTracePivotScaleWitnessFromGeneratedDegree :=
  R.nextPhaseStatus_eq

end GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR

structure GeneratedInteriorTracePivotEntryNonzeroWitnessSM3db2bR
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
  requirement : GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR Cell p A P wp W E K T
  pivotEntry_ne_zero :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry ≠ 0
  pivotEntry_ne_zero_source : SM3db2bRPivotNonzeroSourceStatus
  pivotEntry_ne_zero_bound_to_requirement :
    pivotEntry_ne_zero_source = requirement.pivotNonzeroSourceStatus

namespace GeneratedInteriorTracePivotEntryNonzeroWitnessSM3db2bR

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

theorem pivotEntry_ne_zero_of_witness
    (N : GeneratedInteriorTracePivotEntryNonzeroWitnessSM3db2bR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry ≠ 0 :=
  N.pivotEntry_ne_zero pivot

end GeneratedInteriorTracePivotEntryNonzeroWitnessSM3db2bR

structure GeneratedInteriorTracePivotScaleWitnessSM3db2bR
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
  requirement : GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR Cell p A P wp W E K T
  pivotScale : GeneratedInteriorIndex A → ℝ
  pivotScale_mul_pivotEntry :
    ∀ pivot : GeneratedInteriorIndex A,
      pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1
  pivotEntry_mul_pivotScale :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry * pivotScale pivot = 1
  pivotScaleSourceStatus : SM3db2bRPivotScaleSourceStatus
  pivotScaleSourceStatus_eq :
    pivotScaleSourceStatus =
      SM3db2bRPivotScaleSourceStatus.pivotScaleWitnessMustComeFromGeneratedDegreeProfile

namespace GeneratedInteriorTracePivotScaleWitnessSM3db2bR

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

theorem pivotScale_left_inverse
    (S : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    S.pivotScale pivot * (T.localStepOf pivot).stepUpdate.pivotEntry = 1 :=
  S.pivotScale_mul_pivotEntry pivot

theorem pivotScale_right_inverse
    (S : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry * S.pivotScale pivot = 1 :=
  S.pivotEntry_mul_pivotScale pivot

end GeneratedInteriorTracePivotScaleWitnessSM3db2bR

structure GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR
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
  scaleWitness : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T
  perPivotRegularity :
    ∀ pivot : GeneratedInteriorIndex A,
      GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR
        Cell p A P wp W E K (T.localStepOf pivot)
  traceLocalStepInvariant :
    GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T
  regularityStatus : SM3db2bRPerPivotRegularityStatus
  traceRegularityStatus : SM3db2bRTraceRegularityStatus
  noMatrixInvStatus : SM3db2bRNoMatrixInvStatus
  noTwoSidedInvStatus : SM3db2bRNoTwoSidedInvStatus
  noProductIdentityProofStatus : SM3db2bRNoProductIdentityProofStatus
  noDtnDataStatus : SM3db2bRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2bRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2bRNextPhaseStatus
  perPivotRegularity_eq_from_scaleWitness :
    ∀ pivot : GeneratedInteriorIndex A,
      perPivotRegularity pivot =
        GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR.fromScale
          (scaleWitness.pivotScale pivot)
          (scaleWitness.pivotScale_mul_pivotEntry pivot)
          (scaleWitness.pivotEntry_mul_pivotScale pivot)
  traceLocalStepInvariant_eq_from_perPivotRegularity :
    traceLocalStepInvariant =
      GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR.fromPerPivotRegularity
        scaleWitness.requirement.sourceAudit perPivotRegularity
  regularityStatus_eq :
    regularityStatus = SM3db2bRPerPivotRegularityStatus.perPivotRegularityFromTracePivotScaleWitness
  traceRegularityStatus_eq :
    traceRegularityStatus = SM3db2bRTraceRegularityStatus.traceRegularityFromPerPivotScaleWitness
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2bRNoMatrixInvStatus.noMatrixInvInPerPivotRegularity
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2bRNoTwoSidedInvStatus.noTwoSidedInvInPerPivotRegularity
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2bRNoProductIdentityProofStatus.noProductIdentityProofInPerPivotRegularity
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2bRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2bR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2bRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2bR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2bRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge

namespace GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR

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

def fromTracePivotScaleWitness
    (S : GeneratedInteriorTracePivotScaleWitnessSM3db2bR Cell p A P wp W E K T) :
    GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T where
  scaleWitness := S
  perPivotRegularity := fun pivot =>
    GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR.fromScale
      (S.pivotScale pivot)
      (S.pivotScale_mul_pivotEntry pivot)
      (S.pivotEntry_mul_pivotScale pivot)
  traceLocalStepInvariant :=
    GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR.fromPerPivotRegularity
      S.requirement.sourceAudit
      (fun pivot =>
        GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR.fromScale
          (S.pivotScale pivot)
          (S.pivotScale_mul_pivotEntry pivot)
          (S.pivotEntry_mul_pivotScale pivot))
  regularityStatus := SM3db2bRPerPivotRegularityStatus.perPivotRegularityFromTracePivotScaleWitness
  traceRegularityStatus := SM3db2bRTraceRegularityStatus.traceRegularityFromPerPivotScaleWitness
  noMatrixInvStatus := SM3db2bRNoMatrixInvStatus.noMatrixInvInPerPivotRegularity
  noTwoSidedInvStatus := SM3db2bRNoTwoSidedInvStatus.noTwoSidedInvInPerPivotRegularity
  noProductIdentityProofStatus :=
    SM3db2bRNoProductIdentityProofStatus.noProductIdentityProofInPerPivotRegularity
  noDtnDataStatus := SM3db2bRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2bR
  noArithmeticTargetStatus :=
    SM3db2bRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2bR
  nextPhaseStatus := SM3db2bRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge
  perPivotRegularity_eq_from_scaleWitness := by
    intro pivot
    rfl
  traceLocalStepInvariant_eq_from_perPivotRegularity := by
    rfl
  regularityStatus_eq := by
    rfl
  traceRegularityStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem perPivotRegularity_leftInverse
    (R : GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (R.perPivotRegularity pivot).pivotScale *
        (T.localStepOf pivot).stepUpdate.pivotEntry = 1 :=
  (R.perPivotRegularity pivot).pivotScale_mul_pivotEntry

theorem perPivotRegularity_rightInverse
    (R : GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry *
        (R.perPivotRegularity pivot).pivotScale = 1 :=
  (R.perPivotRegularity pivot).pivotEntry_mul_pivotScale

theorem nextPhase_is_r3c1b1
    (R : GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR Cell p A P wp W E K T) :
    R.nextPhaseStatus =
      SM3db2bRNextPhaseStatus.sm3eRr3c1b1BlockFoldKernelToLocalSchurResidualBridge :=
  R.nextPhaseStatus_eq

end GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR

abbrev RegularGeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotEntryNonzeroRequirementSM3db2bR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTracePivotScaleWitnessSM3db2bR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleWitnessSM3db2bR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTracePivotScaleWitnessSM3db2bR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTracePivotScaleWitnessSM3db2bR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorPerPivotRegularityFromTraceSM3db2bR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorPerPivotRegularityFromTraceSM3db2bR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

end Smoke

end CNNA.PillarA.Arithmetic
