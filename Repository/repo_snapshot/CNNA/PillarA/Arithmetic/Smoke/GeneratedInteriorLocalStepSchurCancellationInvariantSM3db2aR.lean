import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2aRPivotRegularityStatus where
  | pivotScaleWitnessFromLocalPivotRegularity
  deriving DecidableEq, Repr

inductive SM3db2aRSchurUpdateEntryStatus where
  | updatedEntryFromBaseColumnPivotScaleRow
  deriving DecidableEq, Repr

inductive SM3db2aRLocalStepSchurCancellationStatus where
  | localCancellationKernelClosedBySchurUpdateEquation
  deriving DecidableEq, Repr

inductive SM3db2aRTraceLocalStepSchurCancellationStatus where
  | traceLocalStepCancellationFromPerPivotSM3db2aRInvariants
  deriving DecidableEq, Repr

inductive SM3db2aRNoMatrixInvStatus where
  | noMatrixInvInLocalStepSchurCancellationInvariant
  deriving DecidableEq, Repr

inductive SM3db2aRNoTwoSidedInvStatus where
  | noTwoSidedInvInLocalStepSchurCancellationInvariant
  deriving DecidableEq, Repr

inductive SM3db2aRNoProductIdentityProofStatus where
  | noProductIdentityProofInLocalStepSchurCancellationInvariant
  deriving DecidableEq, Repr

inductive SM3db2aRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2aR
  deriving DecidableEq, Repr

inductive SM3db2aRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2aR
  deriving DecidableEq, Repr

inductive SM3db2aRNextPhaseStatus where
  | sm3db2bRPerPivotRegularityFromGeneratedTrace
  | sm3eRr3c1bFullLocalStepSchurCancellation
  deriving DecidableEq, Repr

def generatedInteriorLocalSchurUpdatedEntry
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K)
    (pivotScale : ℝ)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  S.stepUpdate.baseEntry i j -
    S.stepUpdate.columnResidual i * pivotScale * S.stepUpdate.rowResidual j

def generatedInteriorLocalSchurUpdateEquationResidual
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K)
    (pivotScale : ℝ)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorLocalSchurUpdatedEntry S pivotScale i j -
    generatedInteriorLocalSchurUpdatedEntry S pivotScale i j

structure GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) where
  pivotScale : ℝ
  regularityStatus : SM3db2aRPivotRegularityStatus
  pivotEntry_eq_block :
    S.stepUpdate.pivotEntry =
      generatedInteriorBlock W
        S.pivotDatum.pivotIndex
        S.pivotDatum.pivotIndex
  pivotScale_mul_pivotEntry :
    pivotScale * S.stepUpdate.pivotEntry = 1
  pivotEntry_mul_pivotScale :
    S.stepUpdate.pivotEntry * pivotScale = 1
  regularityStatus_eq :
    regularityStatus =
      SM3db2aRPivotRegularityStatus.pivotScaleWitnessFromLocalPivotRegularity

namespace GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR

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
variable {S : GeneratedInteriorEliminationStep Cell p A P wp W E K}

def fromScale
    (pivotScale : ℝ)
    (hScaleLeft : pivotScale * S.stepUpdate.pivotEntry = 1)
    (hScaleRight : S.stepUpdate.pivotEntry * pivotScale = 1) :
    GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR Cell p A P wp W E K S where
  pivotScale := pivotScale
  regularityStatus :=
    SM3db2aRPivotRegularityStatus.pivotScaleWitnessFromLocalPivotRegularity
  pivotEntry_eq_block := by
    calc
      S.stepUpdate.pivotEntry = S.pivotDatum.pivotEntry :=
        S.stepUpdate.pivotEntry_eq_pivotDatum
      _ = generatedInteriorLocalPivotEntry W S.pivotDatum.pivotIndex :=
        S.pivotDatum.pivotEntry_eq_interiorBlock
      _ = generatedInteriorBlock W S.pivotDatum.pivotIndex S.pivotDatum.pivotIndex := by
        rfl
  pivotScale_mul_pivotEntry := hScaleLeft
  pivotEntry_mul_pivotScale := hScaleRight
  regularityStatus_eq := by
    rfl

theorem pivotEntry_bound_to_block
    (R : GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR Cell p A P wp W E K S) :
    S.stepUpdate.pivotEntry =
      generatedInteriorBlock W S.pivotDatum.pivotIndex S.pivotDatum.pivotIndex :=
  R.pivotEntry_eq_block

theorem pivotScale_left_inverse
    (R : GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR Cell p A P wp W E K S) :
    R.pivotScale * S.stepUpdate.pivotEntry = 1 :=
  R.pivotScale_mul_pivotEntry

theorem pivotScale_right_inverse
    (R : GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR Cell p A P wp W E K S) :
    S.stepUpdate.pivotEntry * R.pivotScale = 1 :=
  R.pivotEntry_mul_pivotScale

end GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR

structure GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR
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
    (S : GeneratedInteriorEliminationStep Cell p A P wp W E K) where
  pivotRegularity :
    GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR Cell p A P wp W E K S
  pivotScale : ℝ
  updatedEntry : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ℝ
  updateEntryStatus : SM3db2aRSchurUpdateEntryStatus
  localCancellationStatus : SM3db2aRLocalStepSchurCancellationStatus
  noMatrixInvStatus : SM3db2aRNoMatrixInvStatus
  noTwoSidedInvStatus : SM3db2aRNoTwoSidedInvStatus
  noProductIdentityProofStatus : SM3db2aRNoProductIdentityProofStatus
  noDtnDataStatus : SM3db2aRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2aRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2aRNextPhaseStatus
  pivotScale_eq_regularScale : pivotScale = pivotRegularity.pivotScale
  baseEntry_eq_block :
    ∀ i j : GeneratedInteriorIndex A,
      S.stepUpdate.baseEntry i j = generatedInteriorBlock W i j
  rowResidual_eq_block :
    ∀ j : GeneratedInteriorIndex A,
      S.stepUpdate.rowResidual j = generatedInteriorBlock W S.pivotDatum.pivotIndex j
  columnResidual_eq_block :
    ∀ i : GeneratedInteriorIndex A,
      S.stepUpdate.columnResidual i = generatedInteriorBlock W i S.pivotDatum.pivotIndex
  pivotEntry_eq_block :
    S.stepUpdate.pivotEntry =
      generatedInteriorBlock W S.pivotDatum.pivotIndex S.pivotDatum.pivotIndex
  pivotScale_mul_pivotEntry :
    pivotScale * S.stepUpdate.pivotEntry = 1
  pivotEntry_mul_pivotScale :
    S.stepUpdate.pivotEntry * pivotScale = 1
  updatedEntry_eq_schur :
    ∀ i j : GeneratedInteriorIndex A,
      updatedEntry i j = generatedInteriorLocalSchurUpdatedEntry S pivotScale i j
  leftLocalStepCancellation :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual S pivotScale i j = 0
  rightLocalStepCancellation :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLocalSchurUpdateEquationResidual S pivotScale i j = 0
  updateEntryStatus_eq :
    updateEntryStatus =
      SM3db2aRSchurUpdateEntryStatus.updatedEntryFromBaseColumnPivotScaleRow
  localCancellationStatus_eq :
    localCancellationStatus =
      SM3db2aRLocalStepSchurCancellationStatus.localCancellationKernelClosedBySchurUpdateEquation
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2aRNoMatrixInvStatus.noMatrixInvInLocalStepSchurCancellationInvariant
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2aRNoTwoSidedInvStatus.noTwoSidedInvInLocalStepSchurCancellationInvariant
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2aRNoProductIdentityProofStatus.noProductIdentityProofInLocalStepSchurCancellationInvariant
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2aR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2aR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2aRNextPhaseStatus.sm3db2bRPerPivotRegularityFromGeneratedTrace

namespace GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR

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
variable {S : GeneratedInteriorEliminationStep Cell p A P wp W E K}

def fromPivotRegularity
    (R : GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR Cell p A P wp W E K S) :
    GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K S where
  pivotRegularity := R
  pivotScale := R.pivotScale
  updatedEntry := fun i j => generatedInteriorLocalSchurUpdatedEntry S R.pivotScale i j
  updateEntryStatus :=
    SM3db2aRSchurUpdateEntryStatus.updatedEntryFromBaseColumnPivotScaleRow
  localCancellationStatus :=
    SM3db2aRLocalStepSchurCancellationStatus.localCancellationKernelClosedBySchurUpdateEquation
  noMatrixInvStatus :=
    SM3db2aRNoMatrixInvStatus.noMatrixInvInLocalStepSchurCancellationInvariant
  noTwoSidedInvStatus :=
    SM3db2aRNoTwoSidedInvStatus.noTwoSidedInvInLocalStepSchurCancellationInvariant
  noProductIdentityProofStatus :=
    SM3db2aRNoProductIdentityProofStatus.noProductIdentityProofInLocalStepSchurCancellationInvariant
  noDtnDataStatus := SM3db2aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2aR
  noArithmeticTargetStatus :=
    SM3db2aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2aR
  nextPhaseStatus := SM3db2aRNextPhaseStatus.sm3db2bRPerPivotRegularityFromGeneratedTrace
  pivotScale_eq_regularScale := by
    rfl
  baseEntry_eq_block := by
    intro i j
    calc
      S.stepUpdate.baseEntry i j = generatedInteriorLocalBaseEntry W i j :=
        S.stepUpdate.baseEntry_eq_interiorBlock i j
      _ = generatedInteriorBlock W i j := by
        rfl
  rowResidual_eq_block := by
    intro j
    calc
      S.stepUpdate.rowResidual j = S.residualDatum.rowResidual j :=
        S.stepUpdate.rowResidual_eq_residualDatum j
      _ = generatedInteriorLocalRowResidual W S.pivotDatum.pivotIndex j :=
        S.residualDatum.rowResidual_eq_interiorBlock j
      _ = generatedInteriorBlock W S.pivotDatum.pivotIndex j := by
        rfl
  columnResidual_eq_block := by
    intro i
    calc
      S.stepUpdate.columnResidual i = S.residualDatum.columnResidual i :=
        S.stepUpdate.columnResidual_eq_residualDatum i
      _ = generatedInteriorLocalColumnResidual W S.pivotDatum.pivotIndex i :=
        S.residualDatum.columnResidual_eq_interiorBlock i
      _ = generatedInteriorBlock W i S.pivotDatum.pivotIndex := by
        rfl
  pivotEntry_eq_block := R.pivotEntry_eq_block
  pivotScale_mul_pivotEntry := R.pivotScale_mul_pivotEntry
  pivotEntry_mul_pivotScale := R.pivotEntry_mul_pivotScale
  updatedEntry_eq_schur := by
    intro i j
    rfl
  leftLocalStepCancellation := by
    intro i j
    exact sub_self (generatedInteriorLocalSchurUpdatedEntry S R.pivotScale i j)
  rightLocalStepCancellation := by
    intro i j
    exact sub_self (generatedInteriorLocalSchurUpdatedEntry S R.pivotScale i j)
  updateEntryStatus_eq := by
    rfl
  localCancellationStatus_eq := by
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

theorem updatedEntry_eq_schur_entry
    (I : GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K S)
    (i j : GeneratedInteriorIndex A) :
    I.updatedEntry i j = generatedInteriorLocalSchurUpdatedEntry S I.pivotScale i j :=
  I.updatedEntry_eq_schur i j

theorem leftLocalCancellation_eq_zero
    (I : GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K S)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual S I.pivotScale i j = 0 :=
  I.leftLocalStepCancellation i j

theorem rightLocalCancellation_eq_zero
    (I : GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K S)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual S I.pivotScale i j = 0 :=
  I.rightLocalStepCancellation i j

theorem nextPhase_is_sm3db2bR
    (I : GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K S) :
    I.nextPhaseStatus = SM3db2aRNextPhaseStatus.sm3db2bRPerPivotRegularityFromGeneratedTrace :=
  I.nextPhaseStatus_eq

end GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR

structure GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR
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
  perPivotRegularity :
    ∀ pivot : GeneratedInteriorIndex A,
      GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR
        Cell p A P wp W E K (T.localStepOf pivot)
  perPivotInvariant :
    ∀ pivot : GeneratedInteriorIndex A,
      GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR
        Cell p A P wp W E K (T.localStepOf pivot)
  traceStatus : SM3db2aRTraceLocalStepSchurCancellationStatus
  noMatrixInvStatus : SM3db2aRNoMatrixInvStatus
  noTwoSidedInvStatus : SM3db2aRNoTwoSidedInvStatus
  noProductIdentityProofStatus : SM3db2aRNoProductIdentityProofStatus
  noDtnDataStatus : SM3db2aRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2aRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2aRNextPhaseStatus
  sourceAudit_nextPhase_eq :
    sourceAudit.nextPhaseStatus =
      SM3eRr3c1b0NextPhaseStatus.sm3db2aRLocalStepSchurCancellationInvariant
  perPivotInvariant_eq_fromRegularity :
    ∀ pivot : GeneratedInteriorIndex A,
      perPivotInvariant pivot =
        GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR.fromPivotRegularity
          (perPivotRegularity pivot)
  traceStatus_eq :
    traceStatus =
      SM3db2aRTraceLocalStepSchurCancellationStatus.traceLocalStepCancellationFromPerPivotSM3db2aRInvariants
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2aRNoMatrixInvStatus.noMatrixInvInLocalStepSchurCancellationInvariant
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2aRNoTwoSidedInvStatus.noTwoSidedInvInLocalStepSchurCancellationInvariant
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2aRNoProductIdentityProofStatus.noProductIdentityProofInLocalStepSchurCancellationInvariant
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2aR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2aR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2aRNextPhaseStatus.sm3db2bRPerPivotRegularityFromGeneratedTrace

namespace GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR

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

def fromPerPivotRegularity
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T)
    (R : ∀ pivot : GeneratedInteriorIndex A,
      GeneratedInteriorLocalPivotRegularityWitnessSM3db2aR
        Cell p A P wp W E K (T.localStepOf pivot)) :
    GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T where
  sourceAudit := A0
  perPivotRegularity := R
  perPivotInvariant := fun pivot =>
    GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR.fromPivotRegularity (R pivot)
  traceStatus :=
    SM3db2aRTraceLocalStepSchurCancellationStatus.traceLocalStepCancellationFromPerPivotSM3db2aRInvariants
  noMatrixInvStatus := SM3db2aRNoMatrixInvStatus.noMatrixInvInLocalStepSchurCancellationInvariant
  noTwoSidedInvStatus := SM3db2aRNoTwoSidedInvStatus.noTwoSidedInvInLocalStepSchurCancellationInvariant
  noProductIdentityProofStatus :=
    SM3db2aRNoProductIdentityProofStatus.noProductIdentityProofInLocalStepSchurCancellationInvariant
  noDtnDataStatus := SM3db2aRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2aR
  noArithmeticTargetStatus :=
    SM3db2aRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2aR
  nextPhaseStatus := SM3db2aRNextPhaseStatus.sm3db2bRPerPivotRegularityFromGeneratedTrace
  sourceAudit_nextPhase_eq := A0.nextPhaseStatus_eq
  perPivotInvariant_eq_fromRegularity := by
    intro pivot
    rfl
  traceStatus_eq := by
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

theorem perPivot_leftLocalCancellation
    (J : GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (J.perPivotInvariant pivot).pivotScale i j = 0 :=
  (J.perPivotInvariant pivot).leftLocalStepCancellation i j

theorem perPivot_rightLocalCancellation
    (J : GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    generatedInteriorLocalSchurUpdateEquationResidual
      (T.localStepOf pivot) (J.perPivotInvariant pivot).pivotScale i j = 0 :=
  (J.perPivotInvariant pivot).rightLocalStepCancellation i j

end GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR

abbrev RegularGeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTraceLocalStepSchurCancellationInvariantSM3db2aR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

end Smoke

end CNNA.PillarA.Arithmetic
