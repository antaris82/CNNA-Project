import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db4aVTerminalFoldInductionEquationStatus where
  | terminalFoldInductionEquationCarriedByEquationDatum
  | terminalFoldInductionEquationMissingFromCurrentSM3db4aRAPI
  deriving DecidableEq, Repr

inductive SM3db4aVResidualClosureEquationStatus where
  | residualClosureEquationCarriedByEquationDatum
  | residualClosureEquationMissingFromCurrentSM3db4aRAPI
  deriving DecidableEq, Repr

inductive SM3db4aVFoldOrderCoverageEquationStatus where
  | foldOrderCoverageEquationCarriedByEquationDatum
  | foldOrderCoverageEquationMissingFromCurrentSM3db4aRAPI
  deriving DecidableEq, Repr

inductive SM3db4aVLeftRightTerminalIdentityEquationStatus where
  | separateLeftAndRightTerminalIdentityEquationsCarriedByEquationDatum
  | separateLeftAndRightTerminalIdentityEquationsRequiredBeyondCurrentSM3db4aRAPI
  deriving DecidableEq, Repr

inductive SM3db4aVEquationSourceStatus where
  | terminalFoldResidualIdentityEquationSourceCarriedByDatum
  | terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  deriving DecidableEq, Repr

inductive SM3db4aVCertificateExportStatus where
  | terminalIdentityFieldCertificatePreparedFromEquationSource
  | terminalIdentityFieldCertificateBlockedUntilEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aVNoFreeIdentityFieldStatus where
  | noFreeIdentityFieldsInFinalCertificateAdapter
  deriving DecidableEq, Repr

inductive SM3db4aVNoProductIdentityProofStatus where
  | noProductIdentityProofInTerminalFoldResidualIdentityEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aVNoTwoSidedInvStatus where
  | noTwoSidedInvInTerminalFoldResidualIdentityEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aVNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInTerminalFoldResidualIdentityEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aVNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInTerminalFoldResidualIdentityEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aVNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInTerminalFoldResidualIdentityEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aVNextPhaseStatus where
  | sm3db4aWTerminalIdentityFieldCertificateFromEquationSource
  | sm3eRr3c1dFullTerminalCoverageConsumer
  deriving DecidableEq, Repr

inductive SM3db4aVLedgerStatus where
  | terminalFoldResidualIdentityEquationSourceAuditClosed
  | terminalFoldResidualIdentityEquationSourceCarriedByDatum
  deriving DecidableEq, Repr

structure GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV
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
  terminalFoldInductionEquationStatus : SM3db4aVTerminalFoldInductionEquationStatus
  residualClosureEquationStatus : SM3db4aVResidualClosureEquationStatus
  foldOrderCoverageEquationStatus : SM3db4aVFoldOrderCoverageEquationStatus
  leftRightTerminalIdentityEquationStatus : SM3db4aVLeftRightTerminalIdentityEquationStatus
  leftBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i i = 1
  leftBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorLeftBlockFold W T i j = 0
  rightBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i i = 1
  rightBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorRightBlockFold W T i j = 0
  terminalFoldInductionEquationStatus_eq :
    terminalFoldInductionEquationStatus =
      SM3db4aVTerminalFoldInductionEquationStatus.terminalFoldInductionEquationCarriedByEquationDatum
  residualClosureEquationStatus_eq :
    residualClosureEquationStatus =
      SM3db4aVResidualClosureEquationStatus.residualClosureEquationCarriedByEquationDatum
  foldOrderCoverageEquationStatus_eq :
    foldOrderCoverageEquationStatus =
      SM3db4aVFoldOrderCoverageEquationStatus.foldOrderCoverageEquationCarriedByEquationDatum
  leftRightTerminalIdentityEquationStatus_eq :
    leftRightTerminalIdentityEquationStatus =
      SM3db4aVLeftRightTerminalIdentityEquationStatus.separateLeftAndRightTerminalIdentityEquationsCarriedByEquationDatum

namespace GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV

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

def fromTerminalIdentityEquations
    (leftIdentity :
      ∀ i j : GeneratedInteriorIndex A,
        generatedInteriorLeftBlockFold W T i j =
          (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j)
    (rightIdentity :
      ∀ i j : GeneratedInteriorIndex A,
        generatedInteriorRightBlockFold W T i j =
          (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j)
    (leftDiagonal :
      ∀ i : GeneratedInteriorIndex A,
        generatedInteriorLeftBlockFold W T i i = 1)
    (leftOffdiag :
      ∀ i j : GeneratedInteriorIndex A,
        i ≠ j → generatedInteriorLeftBlockFold W T i j = 0)
    (rightDiagonal :
      ∀ i : GeneratedInteriorIndex A,
        generatedInteriorRightBlockFold W T i i = 1)
    (rightOffdiag :
      ∀ i j : GeneratedInteriorIndex A,
        i ≠ j → generatedInteriorRightBlockFold W T i j = 0) :
    GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T where
  terminalFoldInductionEquationStatus :=
    SM3db4aVTerminalFoldInductionEquationStatus.terminalFoldInductionEquationCarriedByEquationDatum
  residualClosureEquationStatus :=
    SM3db4aVResidualClosureEquationStatus.residualClosureEquationCarriedByEquationDatum
  foldOrderCoverageEquationStatus :=
    SM3db4aVFoldOrderCoverageEquationStatus.foldOrderCoverageEquationCarriedByEquationDatum
  leftRightTerminalIdentityEquationStatus :=
    SM3db4aVLeftRightTerminalIdentityEquationStatus.separateLeftAndRightTerminalIdentityEquationsCarriedByEquationDatum
  leftBlockFold_eq_identity := leftIdentity
  rightBlockFold_eq_identity := rightIdentity
  leftBlockFold_diagonal := leftDiagonal
  leftBlockFold_offdiag := leftOffdiag
  rightBlockFold_diagonal := rightDiagonal
  rightBlockFold_offdiag := rightOffdiag
  terminalFoldInductionEquationStatus_eq := by
    rfl
  residualClosureEquationStatus_eq := by
    rfl
  foldOrderCoverageEquationStatus_eq := by
    rfl
  leftRightTerminalIdentityEquationStatus_eq := by
    rfl

theorem leftIdentity
    (D : GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFold W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.leftBlockFold_eq_identity i j

theorem rightIdentity
    (D : GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFold W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  D.rightBlockFold_eq_identity i j

end GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV

structure GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
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
  identityFieldsAudit : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T
  coverageAudit : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  tracePivotCoverage : GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T
  terminalFoldState : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  terminalFoldInductionEquationStatus : SM3db4aVTerminalFoldInductionEquationStatus
  residualClosureEquationStatus : SM3db4aVResidualClosureEquationStatus
  foldOrderCoverageEquationStatus : SM3db4aVFoldOrderCoverageEquationStatus
  leftRightTerminalIdentityEquationStatus : SM3db4aVLeftRightTerminalIdentityEquationStatus
  equationSourceStatus : SM3db4aVEquationSourceStatus
  certificateExportStatus : SM3db4aVCertificateExportStatus
  nextPhaseStatus : SM3db4aVNextPhaseStatus
  coverageAudit_eq_identityFieldsAudit : coverageAudit = identityFieldsAudit.coverageAudit
  invariance_eq_identityFieldsAudit : invariance = identityFieldsAudit.invariance
  tracePivotCoverage_eq_identityFieldsAudit :
    tracePivotCoverage = identityFieldsAudit.tracePivotCoverage
  terminalFoldState_eq_identityFieldsAudit :
    terminalFoldState = identityFieldsAudit.terminalFoldState
  sm3db4aU_leftSource_missing :
    identityFieldsAudit.leftTerminalIdentityFieldSourceStatus =
      SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  sm3db4aU_rightSource_missing :
    identityFieldsAudit.rightTerminalIdentityFieldSourceStatus =
      SM3db4aUTerminalIdentityFieldSourceStatus.terminalIdentityFieldSourceMissingFromCurrentSM3db4aRAPI
  sm3db4aU_terminalFoldInductionStatus_eq :
    identityFieldsAudit.terminalFoldInductionEquationStatus =
      SM3db4aUTerminalFoldInductionEquationStatus.foldInvarianceAvailableButTerminalIdentityEquationMissing
  sm3db4aU_residualClosureStatus_eq :
    identityFieldsAudit.residualClosureEquationStatus =
      SM3db4aUResidualClosureEquationStatus.residualContributionAvailableButNoIdentityClosureEquation
  sm3db4aU_foldOrderCoverageStatus_eq :
    identityFieldsAudit.foldOrderCoverageEquationStatus =
      SM3db4aUFoldOrderCoverageEquationStatus.foldUpdateOrderAvailableButNoIdentityClosureEquation
  terminalFoldInductionEquationStatus_eq :
    terminalFoldInductionEquationStatus =
      SM3db4aVTerminalFoldInductionEquationStatus.terminalFoldInductionEquationMissingFromCurrentSM3db4aRAPI
  residualClosureEquationStatus_eq :
    residualClosureEquationStatus =
      SM3db4aVResidualClosureEquationStatus.residualClosureEquationMissingFromCurrentSM3db4aRAPI
  foldOrderCoverageEquationStatus_eq :
    foldOrderCoverageEquationStatus =
      SM3db4aVFoldOrderCoverageEquationStatus.foldOrderCoverageEquationMissingFromCurrentSM3db4aRAPI
  leftRightTerminalIdentityEquationStatus_eq :
    leftRightTerminalIdentityEquationStatus =
      SM3db4aVLeftRightTerminalIdentityEquationStatus.separateLeftAndRightTerminalIdentityEquationsRequiredBeyondCurrentSM3db4aRAPI
  equationSourceStatus_eq :
    equationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  certificateExportStatus_eq :
    certificateExportStatus =
      SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificateBlockedUntilEquationSource
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource

namespace GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV

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

def fromIdentityFieldsAudit
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV Cell p A P wp W E K T where
  identityFieldsAudit := A0
  coverageAudit := A0.coverageAudit
  invariance := A0.invariance
  tracePivotCoverage := A0.tracePivotCoverage
  terminalFoldState := A0.terminalFoldState
  terminalFoldInductionEquationStatus :=
    SM3db4aVTerminalFoldInductionEquationStatus.terminalFoldInductionEquationMissingFromCurrentSM3db4aRAPI
  residualClosureEquationStatus :=
    SM3db4aVResidualClosureEquationStatus.residualClosureEquationMissingFromCurrentSM3db4aRAPI
  foldOrderCoverageEquationStatus :=
    SM3db4aVFoldOrderCoverageEquationStatus.foldOrderCoverageEquationMissingFromCurrentSM3db4aRAPI
  leftRightTerminalIdentityEquationStatus :=
    SM3db4aVLeftRightTerminalIdentityEquationStatus.separateLeftAndRightTerminalIdentityEquationsRequiredBeyondCurrentSM3db4aRAPI
  equationSourceStatus :=
    SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  certificateExportStatus :=
    SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificateBlockedUntilEquationSource
  nextPhaseStatus := SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource
  coverageAudit_eq_identityFieldsAudit := by
    rfl
  invariance_eq_identityFieldsAudit := by
    rfl
  tracePivotCoverage_eq_identityFieldsAudit := by
    rfl
  terminalFoldState_eq_identityFieldsAudit := by
    rfl
  sm3db4aU_leftSource_missing := A0.leftTerminalIdentityFieldSourceStatus_eq
  sm3db4aU_rightSource_missing := A0.rightTerminalIdentityFieldSourceStatus_eq
  sm3db4aU_terminalFoldInductionStatus_eq := A0.terminalFoldInductionEquationStatus_eq
  sm3db4aU_residualClosureStatus_eq := A0.residualClosureEquationStatus_eq
  sm3db4aU_foldOrderCoverageStatus_eq := A0.foldOrderCoverageEquationStatus_eq
  terminalFoldInductionEquationStatus_eq := by
    rfl
  residualClosureEquationStatus_eq := by
    rfl
  foldOrderCoverageEquationStatus_eq := by
    rfl
  leftRightTerminalIdentityEquationStatus_eq := by
    rfl
  equationSourceStatus_eq := by
    rfl
  certificateExportStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromCoverageAudit
    (C : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV Cell p A P wp W E K T :=
  fromIdentityFieldsAudit
    (GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU.fromTerminalFoldResidualCoverageAudit C)

theorem equationSource_still_required
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV Cell p A P wp W E K T) :
    A0.equationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU :=
  A0.equationSourceStatus_eq

end GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV

structure GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV
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
  sourceAudit : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV Cell p A P wp W E K T
  equationDatum : GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T
  identityFieldsAudit : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T
  coverageAudit : GeneratedInteriorTerminalFoldResidualCoverageAuditSM3db4aT Cell p A P wp W E K T
  invariance : GeneratedInteriorBlockFoldInvarianceR3c1c Cell p A P wp W E K T
  tracePivotCoverage : GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR Cell p A P wp W E K T
  terminalFoldState : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  equationSourceStatus : SM3db4aVEquationSourceStatus
  certificateExportStatus : SM3db4aVCertificateExportStatus
  noFreeIdentityFieldStatus : SM3db4aVNoFreeIdentityFieldStatus
  noProductIdentityProofStatus : SM3db4aVNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db4aVNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db4aVNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4aVNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4aVNoArithmeticTargetStatus
  nextPhaseStatus : SM3db4aVNextPhaseStatus
  identityFieldsAudit_eq_sourceAudit : identityFieldsAudit = sourceAudit.identityFieldsAudit
  coverageAudit_eq_sourceAudit : coverageAudit = sourceAudit.coverageAudit
  invariance_eq_sourceAudit : invariance = sourceAudit.invariance
  tracePivotCoverage_eq_sourceAudit : tracePivotCoverage = sourceAudit.tracePivotCoverage
  terminalFoldState_eq_sourceAudit : terminalFoldState = sourceAudit.terminalFoldState
  leftBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightBlockFold_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i i = 1
  leftBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorLeftBlockFold W T i j = 0
  rightBlockFold_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i i = 1
  rightBlockFold_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorRightBlockFold W T i j = 0
  leftBlockFold_eq_identity_from_datum :
    ∀ i j : GeneratedInteriorIndex A,
      leftBlockFold_eq_identity i j = equationDatum.leftBlockFold_eq_identity i j
  rightBlockFold_eq_identity_from_datum :
    ∀ i j : GeneratedInteriorIndex A,
      rightBlockFold_eq_identity i j = equationDatum.rightBlockFold_eq_identity i j
  equationSourceStatus_eq :
    equationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceCarriedByDatum
  certificateExportStatus_eq :
    certificateExportStatus =
      SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificatePreparedFromEquationSource
  noFreeIdentityFieldStatus_eq :
    noFreeIdentityFieldStatus =
      SM3db4aVNoFreeIdentityFieldStatus.noFreeIdentityFieldsInFinalCertificateAdapter
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db4aVNoProductIdentityProofStatus.noProductIdentityProofInTerminalFoldResidualIdentityEquationSource
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db4aVNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualIdentityEquationSource
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4aVNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalFoldResidualIdentityEquationSource
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db4aVNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalFoldResidualIdentityEquationSource
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4aVNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalFoldResidualIdentityEquationSource
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource

namespace GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV

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

def fromAuditAndEquationDatum
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV Cell p A P wp W E K T)
    (D : GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T where
  sourceAudit := A0
  equationDatum := D
  identityFieldsAudit := A0.identityFieldsAudit
  coverageAudit := A0.coverageAudit
  invariance := A0.invariance
  tracePivotCoverage := A0.tracePivotCoverage
  terminalFoldState := A0.terminalFoldState
  equationSourceStatus :=
    SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceCarriedByDatum
  certificateExportStatus :=
    SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificatePreparedFromEquationSource
  noFreeIdentityFieldStatus :=
    SM3db4aVNoFreeIdentityFieldStatus.noFreeIdentityFieldsInFinalCertificateAdapter
  noProductIdentityProofStatus :=
    SM3db4aVNoProductIdentityProofStatus.noProductIdentityProofInTerminalFoldResidualIdentityEquationSource
  noTwoSidedInvStatus :=
    SM3db4aVNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualIdentityEquationSource
  noInteriorEliminationDataStatus :=
    SM3db4aVNoInteriorEliminationDataStatus.noInteriorEliminationDataInTerminalFoldResidualIdentityEquationSource
  noDtnDataStatus :=
    SM3db4aVNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInTerminalFoldResidualIdentityEquationSource
  noArithmeticTargetStatus :=
    SM3db4aVNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInTerminalFoldResidualIdentityEquationSource
  nextPhaseStatus := SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource
  identityFieldsAudit_eq_sourceAudit := by
    rfl
  coverageAudit_eq_sourceAudit := by
    rfl
  invariance_eq_sourceAudit := by
    rfl
  tracePivotCoverage_eq_sourceAudit := by
    rfl
  terminalFoldState_eq_sourceAudit := by
    rfl
  leftBlockFold_eq_identity := D.leftBlockFold_eq_identity
  rightBlockFold_eq_identity := D.rightBlockFold_eq_identity
  leftBlockFold_diagonal := D.leftBlockFold_diagonal
  leftBlockFold_offdiag := D.leftBlockFold_offdiag
  rightBlockFold_diagonal := D.rightBlockFold_diagonal
  rightBlockFold_offdiag := D.rightBlockFold_offdiag
  leftBlockFold_eq_identity_from_datum := by
    intro i j
    rfl
  rightBlockFold_eq_identity_from_datum := by
    intro i j
    rfl
  equationSourceStatus_eq := by
    rfl
  certificateExportStatus_eq := by
    rfl
  noFreeIdentityFieldStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

def fromIdentityFieldsAuditAndEquationDatum
    (A0 : GeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU Cell p A P wp W E K T)
    (D : GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T :=
  fromAuditAndEquationDatum
    (GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV.fromIdentityFieldsAudit A0) D

theorem leftBlockFold_entry_eq_identity
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorLeftBlockFold W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  S.leftBlockFold_eq_identity i j

theorem rightBlockFold_entry_eq_identity
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorRightBlockFold W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  S.rightBlockFold_eq_identity i j

theorem noProductIdentityProof
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T) :
    S.noProductIdentityProofStatus =
      SM3db4aVNoProductIdentityProofStatus.noProductIdentityProofInTerminalFoldResidualIdentityEquationSource :=
  S.noProductIdentityProofStatus_eq

theorem noTwoSidedInv
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T) :
    S.noTwoSidedInvStatus =
      SM3db4aVNoTwoSidedInvStatus.noTwoSidedInvInTerminalFoldResidualIdentityEquationSource :=
  S.noTwoSidedInvStatus_eq

end GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV

def terminalFoldResidualIdentityFieldCertificateFromSM3db4aV
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
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T :=
  GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU.fromCoverageAuditAndIdentityFields
    S.coverageAudit
    S.leftBlockFold_eq_identity
    S.rightBlockFold_eq_identity
    S.leftBlockFold_diagonal
    S.leftBlockFold_offdiag
    S.rightBlockFold_diagonal
    S.rightBlockFold_offdiag

abbrev RegularGeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

abbrev RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (A0 : RegularGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU b p wp) :
    RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV b p wp :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV.fromIdentityFieldsAudit A0

def variableTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (A0 : VariableGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU β p wp) :
    VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV β p wp :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV.fromIdentityFieldsAudit A0

def regularTerminalFoldResidualIdentityEquationSourceSM3db4aV
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (A0 : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV b p wp)
    (D : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV b p wp) :
    RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p wp :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV.fromAuditAndEquationDatum A0 D

def variableTerminalFoldResidualIdentityEquationSourceSM3db4aV
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (A0 : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV β p wp)
    (D : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV β p wp) :
    VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p wp :=
  GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV.fromAuditAndEquationDatum A0 D

def regularTerminalFoldResidualIdentityFieldCertificateFromSM3db4aV
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p wp) :
    RegularGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU b p wp :=
  terminalFoldResidualIdentityFieldCertificateFromSM3db4aV S

def variableTerminalFoldResidualIdentityFieldCertificateFromSM3db4aV
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p wp) :
    VariableGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU β p wp :=
  terminalFoldResidualIdentityFieldCertificateFromSM3db4aV S

structure SM3db4aVTerminalFoldResidualIdentityEquationSourceAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAudit : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV b p regularWeight
  variableAudit : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV β p variableWeight
  ledgerStatus : SM3db4aVLedgerStatus
  regularEquationSourceStatus : SM3db4aVEquationSourceStatus
  variableEquationSourceStatus : SM3db4aVEquationSourceStatus
  regularCertificateExportStatus : SM3db4aVCertificateExportStatus
  variableCertificateExportStatus : SM3db4aVCertificateExportStatus
  nextPhaseStatus : SM3db4aVNextPhaseStatus
  regularEquationSourceStatus_eq :
    regularAudit.equationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  variableEquationSourceStatus_eq :
    variableAudit.equationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  ledgerStatus_eq :
    ledgerStatus = SM3db4aVLedgerStatus.terminalFoldResidualIdentityEquationSourceAuditClosed
  regularEquationSourceStatusValue_eq :
    regularEquationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  variableEquationSourceStatusValue_eq :
    variableEquationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  regularCertificateExportStatusValue_eq :
    regularCertificateExportStatus =
      SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificateBlockedUntilEquationSource
  variableCertificateExportStatusValue_eq :
    variableCertificateExportStatus =
      SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificateBlockedUntilEquationSource
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource

namespace SM3db4aVTerminalFoldResidualIdentityEquationSourceAuditLedger

def fromRegularAndVariableIdentityFieldAudits
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularIdentityFieldsAudit : RegularGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU b p regularWeight)
    (variableIdentityFieldsAudit : VariableGeneratedInteriorTerminalFoldResidualIdentityFieldsAuditSM3db4aU β p variableWeight) :
    SM3db4aVTerminalFoldResidualIdentityEquationSourceAuditLedger b β p regularWeight variableWeight where
  regularAudit := regularTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV regularIdentityFieldsAudit
  variableAudit := variableTerminalFoldResidualIdentityEquationSourceAuditSM3db4aV variableIdentityFieldsAudit
  ledgerStatus := SM3db4aVLedgerStatus.terminalFoldResidualIdentityEquationSourceAuditClosed
  regularEquationSourceStatus :=
    SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  variableEquationSourceStatus :=
    SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceRequiredBeyondCurrentSM3db4aU
  regularCertificateExportStatus :=
    SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificateBlockedUntilEquationSource
  variableCertificateExportStatus :=
    SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificateBlockedUntilEquationSource
  nextPhaseStatus := SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource
  regularEquationSourceStatus_eq := by
    rfl
  variableEquationSourceStatus_eq := by
    rfl
  ledgerStatus_eq := by
    rfl
  regularEquationSourceStatusValue_eq := by
    rfl
  variableEquationSourceStatusValue_eq := by
    rfl
  regularCertificateExportStatusValue_eq := by
    rfl
  variableCertificateExportStatusValue_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3db4aVTerminalFoldResidualIdentityEquationSourceAuditLedger

structure SM3db4aVTerminalFoldResidualIdentityEquationSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularSource : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p regularWeight
  variableSource : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p variableWeight
  ledgerStatus : SM3db4aVLedgerStatus
  regularCertificate : RegularGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU b p regularWeight
  variableCertificate : VariableGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU β p variableWeight
  nextPhaseStatus : SM3db4aVNextPhaseStatus
  regularCertificate_eq_source :
    regularCertificate = regularTerminalFoldResidualIdentityFieldCertificateFromSM3db4aV regularSource
  variableCertificate_eq_source :
    variableCertificate = variableTerminalFoldResidualIdentityFieldCertificateFromSM3db4aV variableSource
  ledgerStatus_eq :
    ledgerStatus = SM3db4aVLedgerStatus.terminalFoldResidualIdentityEquationSourceCarriedByDatum
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource

namespace SM3db4aVTerminalFoldResidualIdentityEquationSourceLedger

def fromRegularAndVariableSources
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularSource : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p regularWeight)
    (variableSource : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p variableWeight) :
    SM3db4aVTerminalFoldResidualIdentityEquationSourceLedger b β p regularWeight variableWeight where
  regularSource := regularSource
  variableSource := variableSource
  ledgerStatus := SM3db4aVLedgerStatus.terminalFoldResidualIdentityEquationSourceCarriedByDatum
  regularCertificate := regularTerminalFoldResidualIdentityFieldCertificateFromSM3db4aV regularSource
  variableCertificate := variableTerminalFoldResidualIdentityFieldCertificateFromSM3db4aV variableSource
  nextPhaseStatus := SM3db4aVNextPhaseStatus.sm3db4aWTerminalIdentityFieldCertificateFromEquationSource
  regularCertificate_eq_source := by
    rfl
  variableCertificate_eq_source := by
    rfl
  ledgerStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3db4aVTerminalFoldResidualIdentityEquationSourceLedger

end Smoke

end CNNA.PillarA.Arithmetic
