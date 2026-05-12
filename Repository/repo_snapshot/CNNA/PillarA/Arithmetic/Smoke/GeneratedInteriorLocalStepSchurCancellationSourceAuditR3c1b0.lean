import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3c1b0SourceAuditStatus where
  | localStepSchurCancellationSourceAuditFromSM3db2RAndR3c1a
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0PositiveSourceStatus where
  | baseRowColumnAndPivotEntriesExposedFromSM3db2R
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0MissingPivotScaleStatus where
  | missingPivotScaleInCurrentSM3db2R
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0MissingUpdatedEntryStatus where
  | missingUpdatedEntryInCurrentSM3db2R
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0MissingSchurUpdateEquationStatus where
  | missingUpdatedEntryEqSchurInCurrentSM3db2R
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0MissingLeftLocalCancellationStatus where
  | missingLeftLocalStepCancellationInCurrentSM3db2R
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0MissingRightLocalCancellationStatus where
  | missingRightLocalStepCancellationInCurrentSM3db2R
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0NextPhaseStatus where
  | sm3db2aRLocalStepSchurCancellationInvariant
  deriving DecidableEq, Repr

inductive SM3eRr3c1b0NoIdentityStatus where
  | noBlockFoldIdentityInR3c1b0
  deriving DecidableEq, Repr

structure GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0
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
  blockFoldNormalForm : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T
  sourceAuditStatus : SM3eRr3c1b0SourceAuditStatus
  positiveSourceStatus : SM3eRr3c1b0PositiveSourceStatus
  missingPivotScaleStatus : SM3eRr3c1b0MissingPivotScaleStatus
  missingUpdatedEntryStatus : SM3eRr3c1b0MissingUpdatedEntryStatus
  missingSchurUpdateEquationStatus : SM3eRr3c1b0MissingSchurUpdateEquationStatus
  missingLeftLocalCancellationStatus : SM3eRr3c1b0MissingLeftLocalCancellationStatus
  missingRightLocalCancellationStatus : SM3eRr3c1b0MissingRightLocalCancellationStatus
  noIdentityStatus : SM3eRr3c1b0NoIdentityStatus
  noMatrixInvStatus : SM3db2RNoMatrixInvStatus
  noGlobalInverseStatus : SM3db2RNoGlobalInverseStatus
  noCertificateStatus : SM3db2RNoCertificateStatus
  noTwoSidedInvStatus : SM3db2RNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2RNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1b0NextPhaseStatus
  blockFoldAccumulatedTraceEvaluation_is_fromTrace :
    blockFoldNormalForm.accumulatedTraceEvaluation =
      GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T
  blockFoldAccumulatedEntryFold_is_fromTrace :
    blockFoldNormalForm.accumulatedEntryFold =
      GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  has_baseEntry_eq_block :
    ∀ pivot i j : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.baseEntry i j = generatedInteriorBlock W i j
  has_rowResidual_eq_block :
    ∀ pivot j : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.rowResidual j =
        generatedInteriorBlock W (T.localStepOf pivot).pivotDatum.pivotIndex j
  has_columnResidual_eq_block :
    ∀ pivot i : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.columnResidual i =
        generatedInteriorBlock W i (T.localStepOf pivot).pivotDatum.pivotIndex
  has_pivotEntry_eq_block :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedInteriorBlock W
          (T.localStepOf pivot).pivotDatum.pivotIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex
  localStepStatus_eq_SM3db2R :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepStatus =
        SM3db2REliminationStepStatus.generatedInteriorEliminationLocalStepClosed
  stepUpdateStatus_eq_SM3db2R :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.stepUpdateStatus =
        SM3db2RStepUpdateStatus.stepUpdateFromSM3cRSM3dRCandidate
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  noGlobalInverseStatus_eq :
    noGlobalInverseStatus = SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep
  noCertificateStatus_eq :
    noCertificateStatus = SM3db2RNoCertificateStatus.noCertificateForEliminationStep
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2RNoTwoSidedInvStatus.noTwoSidedInvInSM3db2R
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2R
  sourceAuditStatus_eq :
    sourceAuditStatus =
      SM3eRr3c1b0SourceAuditStatus.localStepSchurCancellationSourceAuditFromSM3db2RAndR3c1a
  positiveSourceStatus_eq :
    positiveSourceStatus =
      SM3eRr3c1b0PositiveSourceStatus.baseRowColumnAndPivotEntriesExposedFromSM3db2R
  missingPivotScaleStatus_eq :
    missingPivotScaleStatus =
      SM3eRr3c1b0MissingPivotScaleStatus.missingPivotScaleInCurrentSM3db2R
  missingUpdatedEntryStatus_eq :
    missingUpdatedEntryStatus =
      SM3eRr3c1b0MissingUpdatedEntryStatus.missingUpdatedEntryInCurrentSM3db2R
  missingSchurUpdateEquationStatus_eq :
    missingSchurUpdateEquationStatus =
      SM3eRr3c1b0MissingSchurUpdateEquationStatus.missingUpdatedEntryEqSchurInCurrentSM3db2R
  missingLeftLocalCancellationStatus_eq :
    missingLeftLocalCancellationStatus =
      SM3eRr3c1b0MissingLeftLocalCancellationStatus.missingLeftLocalStepCancellationInCurrentSM3db2R
  missingRightLocalCancellationStatus_eq :
    missingRightLocalCancellationStatus =
      SM3eRr3c1b0MissingRightLocalCancellationStatus.missingRightLocalStepCancellationInCurrentSM3db2R
  noIdentityStatus_eq :
    noIdentityStatus = SM3eRr3c1b0NoIdentityStatus.noBlockFoldIdentityInR3c1b0
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRr3c1b0NextPhaseStatus.sm3db2aRLocalStepSchurCancellationInvariant

namespace GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0

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

def fromBlockFoldNormalForm
    (N : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T) :
    GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T where
  blockFoldNormalForm := N
  sourceAuditStatus :=
    SM3eRr3c1b0SourceAuditStatus.localStepSchurCancellationSourceAuditFromSM3db2RAndR3c1a
  positiveSourceStatus :=
    SM3eRr3c1b0PositiveSourceStatus.baseRowColumnAndPivotEntriesExposedFromSM3db2R
  missingPivotScaleStatus :=
    SM3eRr3c1b0MissingPivotScaleStatus.missingPivotScaleInCurrentSM3db2R
  missingUpdatedEntryStatus :=
    SM3eRr3c1b0MissingUpdatedEntryStatus.missingUpdatedEntryInCurrentSM3db2R
  missingSchurUpdateEquationStatus :=
    SM3eRr3c1b0MissingSchurUpdateEquationStatus.missingUpdatedEntryEqSchurInCurrentSM3db2R
  missingLeftLocalCancellationStatus :=
    SM3eRr3c1b0MissingLeftLocalCancellationStatus.missingLeftLocalStepCancellationInCurrentSM3db2R
  missingRightLocalCancellationStatus :=
    SM3eRr3c1b0MissingRightLocalCancellationStatus.missingRightLocalStepCancellationInCurrentSM3db2R
  noIdentityStatus := SM3eRr3c1b0NoIdentityStatus.noBlockFoldIdentityInR3c1b0
  noMatrixInvStatus := SM3db2RNoMatrixInvStatus.noMatrixInvForEliminationStep
  noGlobalInverseStatus := SM3db2RNoGlobalInverseStatus.noGlobalInverseForEliminationStep
  noCertificateStatus := SM3db2RNoCertificateStatus.noCertificateForEliminationStep
  noTwoSidedInvStatus := SM3db2RNoTwoSidedInvStatus.noTwoSidedInvInSM3db2R
  noDtnDataStatus := SM3db2RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2R
  noArithmeticTargetStatus :=
    SM3db2RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2R
  nextPhaseStatus := SM3eRr3c1b0NextPhaseStatus.sm3db2aRLocalStepSchurCancellationInvariant
  blockFoldAccumulatedTraceEvaluation_is_fromTrace :=
    N.accumulatedTraceEvaluation_is_fromTrace
  blockFoldAccumulatedEntryFold_is_fromTrace :=
    N.accumulatedEntryFold_is_fromTrace
  trace_source_eq_SM3db3R := T.sourceStatus_eq
  has_baseEntry_eq_block := by
    intro pivot i j
    exact (T.localStepOf pivot).stepUpdate.baseEntry_eq_interiorBlock i j
  has_rowResidual_eq_block := by
    intro pivot j
    calc
      (T.localStepOf pivot).stepUpdate.rowResidual j =
          (T.localStepOf pivot).residualDatum.rowResidual j :=
        (T.localStepOf pivot).stepUpdate.rowResidual_eq_residualDatum j
      _ = generatedInteriorLocalRowResidual W (T.localStepOf pivot).pivotDatum.pivotIndex j :=
        (T.localStepOf pivot).residualDatum.rowResidual_eq_interiorBlock j
      _ = generatedInteriorBlock W (T.localStepOf pivot).pivotDatum.pivotIndex j := by
        rfl
  has_columnResidual_eq_block := by
    intro pivot i
    calc
      (T.localStepOf pivot).stepUpdate.columnResidual i =
          (T.localStepOf pivot).residualDatum.columnResidual i :=
        (T.localStepOf pivot).stepUpdate.columnResidual_eq_residualDatum i
      _ = generatedInteriorLocalColumnResidual W (T.localStepOf pivot).pivotDatum.pivotIndex i :=
        (T.localStepOf pivot).residualDatum.columnResidual_eq_interiorBlock i
      _ = generatedInteriorBlock W i (T.localStepOf pivot).pivotDatum.pivotIndex := by
        rfl
  has_pivotEntry_eq_block := by
    intro pivot
    calc
      (T.localStepOf pivot).stepUpdate.pivotEntry =
          (T.localStepOf pivot).pivotDatum.pivotEntry :=
        (T.localStepOf pivot).stepUpdate.pivotEntry_eq_pivotDatum
      _ = generatedInteriorLocalPivotEntry W (T.localStepOf pivot).pivotDatum.pivotIndex :=
        (T.localStepOf pivot).pivotDatum.pivotEntry_eq_interiorBlock
      _ = generatedInteriorBlock W
          (T.localStepOf pivot).pivotDatum.pivotIndex
          (T.localStepOf pivot).pivotDatum.pivotIndex := by
        rfl
  localStepStatus_eq_SM3db2R := by
    intro pivot
    exact (T.localStepOf pivot).stepStatus_eq
  stepUpdateStatus_eq_SM3db2R := by
    intro pivot
    exact (T.localStepOf pivot).stepUpdate.stepUpdateStatus_eq
  noMatrixInvStatus_eq := by
    rfl
  noGlobalInverseStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  sourceAuditStatus_eq := by
    rfl
  positiveSourceStatus_eq := by
    rfl
  missingPivotScaleStatus_eq := by
    rfl
  missingUpdatedEntryStatus_eq := by
    rfl
  missingSchurUpdateEquationStatus_eq := by
    rfl
  missingLeftLocalCancellationStatus_eq := by
    rfl
  missingRightLocalCancellationStatus_eq := by
    rfl
  noIdentityStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromEliminationTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T :=
  fromBlockFoldNormalForm (GeneratedInteriorBlockFoldNormalFormR3c1a.fromEliminationTrace T)

theorem baseEntry_eq_block
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T)
    (pivot i j : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.baseEntry i j = generatedInteriorBlock W i j :=
  A0.has_baseEntry_eq_block pivot i j

theorem rowResidual_eq_block
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T)
    (pivot j : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.rowResidual j =
      generatedInteriorBlock W (T.localStepOf pivot).pivotDatum.pivotIndex j :=
  A0.has_rowResidual_eq_block pivot j

theorem columnResidual_eq_block
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T)
    (pivot i : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.columnResidual i =
      generatedInteriorBlock W i (T.localStepOf pivot).pivotDatum.pivotIndex :=
  A0.has_columnResidual_eq_block pivot i

theorem pivotEntry_eq_block
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry =
      generatedInteriorBlock W
        (T.localStepOf pivot).pivotDatum.pivotIndex
        (T.localStepOf pivot).pivotDatum.pivotIndex :=
  A0.has_pivotEntry_eq_block pivot

theorem nextPhase_is_SM3db2aR
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T) :
    A0.nextPhaseStatus =
      SM3eRr3c1b0NextPhaseStatus.sm3db2aRLocalStepSchurCancellationInvariant :=
  A0.nextPhaseStatus_eq

end GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0

abbrev RegularGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularLocalStepSchurCancellationSourceAuditR3c1b0
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    RegularGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 b p wp :=
  GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0.fromEliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableLocalStepSchurCancellationSourceAuditR3c1b0
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    VariableGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 β p wp :=
  GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0.fromEliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAudit : RegularGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 b p regularWeight
  variableAudit : VariableGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 β p variableWeight
  regularNextPhase_eq :
    regularAudit.nextPhaseStatus =
      SM3eRr3c1b0NextPhaseStatus.sm3db2aRLocalStepSchurCancellationInvariant
  variableNextPhase_eq :
    variableAudit.nextPhaseStatus =
      SM3eRr3c1b0NextPhaseStatus.sm3db2aRLocalStepSchurCancellationInvariant
  regularMissingPivotScale_eq :
    regularAudit.missingPivotScaleStatus =
      SM3eRr3c1b0MissingPivotScaleStatus.missingPivotScaleInCurrentSM3db2R
  variableMissingPivotScale_eq :
    variableAudit.missingPivotScaleStatus =
      SM3eRr3c1b0MissingPivotScaleStatus.missingPivotScaleInCurrentSM3db2R
  regularMissingUpdatedEntry_eq :
    regularAudit.missingUpdatedEntryStatus =
      SM3eRr3c1b0MissingUpdatedEntryStatus.missingUpdatedEntryInCurrentSM3db2R
  variableMissingUpdatedEntry_eq :
    variableAudit.missingUpdatedEntryStatus =
      SM3eRr3c1b0MissingUpdatedEntryStatus.missingUpdatedEntryInCurrentSM3db2R
  regularMissingSchurUpdate_eq :
    regularAudit.missingSchurUpdateEquationStatus =
      SM3eRr3c1b0MissingSchurUpdateEquationStatus.missingUpdatedEntryEqSchurInCurrentSM3db2R
  variableMissingSchurUpdate_eq :
    variableAudit.missingSchurUpdateEquationStatus =
      SM3eRr3c1b0MissingSchurUpdateEquationStatus.missingUpdatedEntryEqSchurInCurrentSM3db2R

namespace SM3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger

def fromRegularAndVariable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularAudit : RegularGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 b p regularWeight)
    (variableAudit : VariableGeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 β p variableWeight) :
    SM3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger
      b β p regularWeight variableWeight where
  regularAudit := regularAudit
  variableAudit := variableAudit
  regularNextPhase_eq := regularAudit.nextPhaseStatus_eq
  variableNextPhase_eq := variableAudit.nextPhaseStatus_eq
  regularMissingPivotScale_eq := regularAudit.missingPivotScaleStatus_eq
  variableMissingPivotScale_eq := variableAudit.missingPivotScaleStatus_eq
  regularMissingUpdatedEntry_eq := regularAudit.missingUpdatedEntryStatus_eq
  variableMissingUpdatedEntry_eq := variableAudit.missingUpdatedEntryStatus_eq
  regularMissingSchurUpdate_eq := regularAudit.missingSchurUpdateEquationStatus_eq
  variableMissingSchurUpdate_eq := variableAudit.missingSchurUpdateEquationStatus_eq

end SM3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger

def sm3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger
      b β p regularWeight variableWeight :=
  SM3eRr3c1b0LocalStepSchurCancellationSourceAuditLedger.fromRegularAndVariable
    (regularLocalStepSchurCancellationSourceAuditR3c1b0 b p regularWeight)
    (variableLocalStepSchurCancellationSourceAuditR3c1b0 β p variableWeight)

end Smoke

end CNNA.PillarA.Arithmetic
