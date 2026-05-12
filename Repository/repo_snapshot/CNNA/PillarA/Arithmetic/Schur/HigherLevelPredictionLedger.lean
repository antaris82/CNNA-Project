import CNNA.PillarA.Arithmetic.Schur.IdentityLedger

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive HigherLevelFactorDegreeCandidateStatus where
  | noFactorDegreeBeforeAR11Certificate
  deriving DecidableEq, Repr

inductive HigherLevelDiscriminantCandidateStatus where
  | noDiscriminantBeforeAR11Certificate
  deriving DecidableEq, Repr

inductive HigherLevelHeegnerCandidateStatus where
  | noHeegnerCandidateBeforeAR11Certificate
  deriving DecidableEq, Repr

inductive HigherLevelPredictionStatus where
  | openPrediction
  | theoremCertified
  | refuted
  deriving DecidableEq, Repr

inductive HigherLevelAR11CertificateReferenceStatus where
  | noAR11CertificateYet
  | theoremCertificateAvailable
  | refutationCertificateAvailable
  deriving DecidableEq, Repr

inductive HigherLevelTestPowerStatus where
  | diagnosticOnlyNoProofPower
  deriving DecidableEq, Repr

inductive HigherLevelCalibrationStatus where
  | l2L3CalibrationOnlyNoExtrapolationRule
  deriving DecidableEq, Repr

inductive HigherLevelDownstreamDisciplineStatus where
  | noPredictionRowMayServeAsInputForAR11ToAR16
  deriving DecidableEq, Repr

inductive HigherLevelBoundaryDisciplineStatus where
  | recursiveBoundarySourceOnlyNoCutSpecFullFallback
  deriving DecidableEq, Repr

structure HigherLevelPredictionRow
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L) where
  boundarySource : BoundarySource.BoundarySourceSurface source L
  boundarySource_eq : boundarySource = B
  branchingParameter : Nat
  branchingParameter_eq : branchingParameter = b
  levelGreaterThanThree : 3 < L
  recurrenceLedger : SchurMobiusRecurrenceLedger source L
  recurrenceLedger_eq : recurrenceLedger = SchurMobiusRecurrenceLedger.fromBoundarySource B
  recurrenceClosed :
    recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  factorDegreeCandidate : Option Nat
  factorDegreeCandidate_eq : factorDegreeCandidate = none
  factorDegreeStatus : HigherLevelFactorDegreeCandidateStatus
  factorDegreeStatus_eq :
    factorDegreeStatus =
      HigherLevelFactorDegreeCandidateStatus.noFactorDegreeBeforeAR11Certificate
  discriminantCandidate : Option ℤ
  discriminantCandidate_eq : discriminantCandidate = none
  discriminantStatus : HigherLevelDiscriminantCandidateStatus
  discriminantStatus_eq :
    discriminantStatus =
      HigherLevelDiscriminantCandidateStatus.noDiscriminantBeforeAR11Certificate
  heegnerCandidate : Option Nat
  heegnerCandidate_eq : heegnerCandidate = none
  heegnerStatus : HigherLevelHeegnerCandidateStatus
  heegnerStatus_eq :
    heegnerStatus =
      HigherLevelHeegnerCandidateStatus.noHeegnerCandidateBeforeAR11Certificate
  predictionStatus : HigherLevelPredictionStatus
  predictionStatus_eq : predictionStatus = HigherLevelPredictionStatus.openPrediction
  ar11CertificateReferenceStatus : HigherLevelAR11CertificateReferenceStatus
  ar11CertificateReferenceStatus_eq :
    ar11CertificateReferenceStatus =
      HigherLevelAR11CertificateReferenceStatus.noAR11CertificateYet
  testPowerStatus : HigherLevelTestPowerStatus
  testPowerStatus_eq :
    testPowerStatus = HigherLevelTestPowerStatus.diagnosticOnlyNoProofPower
  calibrationStatus : HigherLevelCalibrationStatus
  calibrationStatus_eq :
    calibrationStatus =
      HigherLevelCalibrationStatus.l2L3CalibrationOnlyNoExtrapolationRule
  downstreamDisciplineStatus : HigherLevelDownstreamDisciplineStatus
  downstreamDisciplineStatus_eq :
    downstreamDisciplineStatus =
      HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16
  boundaryDisciplineStatus : HigherLevelBoundaryDisciplineStatus
  boundaryDisciplineStatus_eq :
    boundaryDisciplineStatus =
      HigherLevelBoundaryDisciplineStatus.recursiveBoundarySourceOnlyNoCutSpecFullFallback
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T
  l2CalibrationDiscriminant : l2EisensteinNormDiscriminant = -3
  l3CalibrationDiscriminant : l3GaussianNormDiscriminant = -4

namespace HigherLevelPredictionRow

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L}

def openFromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L) :
    HigherLevelPredictionRow B b hL where
  boundarySource := B
  boundarySource_eq := by
    rfl
  branchingParameter := b
  branchingParameter_eq := by
    rfl
  levelGreaterThanThree := hL
  recurrenceLedger := SchurMobiusRecurrenceLedger.fromBoundarySource B
  recurrenceLedger_eq := by
    rfl
  recurrenceClosed := by
    rfl
  factorDegreeCandidate := none
  factorDegreeCandidate_eq := by
    rfl
  factorDegreeStatus :=
    HigherLevelFactorDegreeCandidateStatus.noFactorDegreeBeforeAR11Certificate
  factorDegreeStatus_eq := by
    rfl
  discriminantCandidate := none
  discriminantCandidate_eq := by
    rfl
  discriminantStatus :=
    HigherLevelDiscriminantCandidateStatus.noDiscriminantBeforeAR11Certificate
  discriminantStatus_eq := by
    rfl
  heegnerCandidate := none
  heegnerCandidate_eq := by
    rfl
  heegnerStatus :=
    HigherLevelHeegnerCandidateStatus.noHeegnerCandidateBeforeAR11Certificate
  heegnerStatus_eq := by
    rfl
  predictionStatus := HigherLevelPredictionStatus.openPrediction
  predictionStatus_eq := by
    rfl
  ar11CertificateReferenceStatus := HigherLevelAR11CertificateReferenceStatus.noAR11CertificateYet
  ar11CertificateReferenceStatus_eq := by
    rfl
  testPowerStatus := HigherLevelTestPowerStatus.diagnosticOnlyNoProofPower
  testPowerStatus_eq := by
    rfl
  calibrationStatus := HigherLevelCalibrationStatus.l2L3CalibrationOnlyNoExtrapolationRule
  calibrationStatus_eq := by
    rfl
  downstreamDisciplineStatus :=
    HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16
  downstreamDisciplineStatus_eq := by
    rfl
  boundaryDisciplineStatus :=
    HigherLevelBoundaryDisciplineStatus.recursiveBoundarySourceOnlyNoCutSpecFullFallback
  boundaryDisciplineStatus_eq := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  l2CalibrationDiscriminant := l2EisensteinNormDiscriminant_eq_neg_three
  l3CalibrationDiscriminant := l3GaussianNormDiscriminant_eq_neg_four

theorem prediction_status_open
    (R : HigherLevelPredictionRow B b hL) :
    R.predictionStatus = HigherLevelPredictionStatus.openPrediction :=
  R.predictionStatus_eq

theorem no_ar11_certificate_yet
    (R : HigherLevelPredictionRow B b hL) :
    R.ar11CertificateReferenceStatus =
      HigherLevelAR11CertificateReferenceStatus.noAR11CertificateYet :=
  R.ar11CertificateReferenceStatus_eq

theorem factor_degree_not_certified
    (R : HigherLevelPredictionRow B b hL) :
    R.factorDegreeCandidate = none :=
  R.factorDegreeCandidate_eq

theorem discriminant_not_certified
    (R : HigherLevelPredictionRow B b hL) :
    R.discriminantCandidate = none :=
  R.discriminantCandidate_eq

theorem heegner_not_certified
    (R : HigherLevelPredictionRow B b hL) :
    R.heegnerCandidate = none :=
  R.heegnerCandidate_eq

theorem diagnostic_only
    (R : HigherLevelPredictionRow B b hL) :
    R.testPowerStatus = HigherLevelTestPowerStatus.diagnosticOnlyNoProofPower :=
  R.testPowerStatus_eq

theorem no_downstream_input
    (R : HigherLevelPredictionRow B b hL) :
    R.downstreamDisciplineStatus =
      HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16 :=
  R.downstreamDisciplineStatus_eq

theorem l2_l3_calibration_only
    (R : HigherLevelPredictionRow B b hL) :
    R.calibrationStatus =
      HigherLevelCalibrationStatus.l2L3CalibrationOnlyNoExtrapolationRule :=
  R.calibrationStatus_eq

theorem route_recursiveHistory
    (R : HigherLevelPredictionRow B b hL) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  R.route

theorem noCutSpecCarrierClaim_at
    (R : HigherLevelPredictionRow B b hL)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  R.noCutSpecCarrierClaim k

end HigherLevelPredictionRow

inductive HigherLevelPredictionLedgerStatus where
  | ar10cHigherLevelPredictionLedgerOpen
  deriving DecidableEq, Repr

structure HigherLevelPredictionLedger
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L) where
  row : HigherLevelPredictionRow B b hL
  row_eq : row = HigherLevelPredictionRow.openFromBoundarySource B b hL
  ledgerStatus : HigherLevelPredictionLedgerStatus
  ledgerStatus_eq :
    ledgerStatus =
      HigherLevelPredictionLedgerStatus.ar10cHigherLevelPredictionLedgerOpen
  rowOpen : row.predictionStatus = HigherLevelPredictionStatus.openPrediction
  rowDiagnosticOnly : row.testPowerStatus = HigherLevelTestPowerStatus.diagnosticOnlyNoProofPower
  rowNoAR11Certificate :
    row.ar11CertificateReferenceStatus =
      HigherLevelAR11CertificateReferenceStatus.noAR11CertificateYet
  rowNoDownstreamInput :
    row.downstreamDisciplineStatus =
      HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16
  rowNoFactorDegree : row.factorDegreeCandidate = none
  rowNoDiscriminant : row.discriminantCandidate = none
  rowNoHeegner : row.heegnerCandidate = none
  rowRoute : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  rowLevelGreaterThanThree : 3 < L

namespace HigherLevelPredictionLedger

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L) :
    HigherLevelPredictionLedger B b hL :=
  let row := HigherLevelPredictionRow.openFromBoundarySource B b hL
  {
    row := row
    row_eq := by
      rfl
    ledgerStatus := HigherLevelPredictionLedgerStatus.ar10cHigherLevelPredictionLedgerOpen
    ledgerStatus_eq := by
      rfl
    rowOpen := HigherLevelPredictionRow.prediction_status_open row
    rowDiagnosticOnly := HigherLevelPredictionRow.diagnostic_only row
    rowNoAR11Certificate := HigherLevelPredictionRow.no_ar11_certificate_yet row
    rowNoDownstreamInput := HigherLevelPredictionRow.no_downstream_input row
    rowNoFactorDegree := HigherLevelPredictionRow.factor_degree_not_certified row
    rowNoDiscriminant := HigherLevelPredictionRow.discriminant_not_certified row
    rowNoHeegner := HigherLevelPredictionRow.heegner_not_certified row
    rowRoute := HigherLevelPredictionRow.route_recursiveHistory row
    rowLevelGreaterThanThree := row.levelGreaterThanThree
  }

theorem ledger_status_open
    (Ldg : HigherLevelPredictionLedger B b hL) :
    Ldg.ledgerStatus =
      HigherLevelPredictionLedgerStatus.ar10cHigherLevelPredictionLedgerOpen :=
  Ldg.ledgerStatus_eq

theorem row_status_open
    (Ldg : HigherLevelPredictionLedger B b hL) :
    Ldg.row.predictionStatus = HigherLevelPredictionStatus.openPrediction :=
  Ldg.rowOpen

theorem row_no_ar11_certificate
    (Ldg : HigherLevelPredictionLedger B b hL) :
    Ldg.row.ar11CertificateReferenceStatus =
      HigherLevelAR11CertificateReferenceStatus.noAR11CertificateYet :=
  Ldg.rowNoAR11Certificate

theorem row_no_downstream_input
    (Ldg : HigherLevelPredictionLedger B b hL) :
    Ldg.row.downstreamDisciplineStatus =
      HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16 :=
  Ldg.rowNoDownstreamInput

end HigherLevelPredictionLedger

abbrev HigherLevelBoundaryFamily
    (source : ArithmeticSource Cell T) :=
  (L : Nat) → 3 < L → BoundarySource.BoundarySourceSurface source L

abbrev HigherLevelPredictionTestMatrix
    (boundaryAt : HigherLevelBoundaryFamily source) :=
  (b : Nat) → (L : Nat) → (hL : 3 < L) →
    HigherLevelPredictionLedger (boundaryAt L hL) b hL

namespace HigherLevelPredictionTestMatrix

def fromBoundaryFamily
    (boundaryAt : HigherLevelBoundaryFamily source) :
    HigherLevelPredictionTestMatrix boundaryAt :=
  fun b L hL => HigherLevelPredictionLedger.fromBoundarySource (boundaryAt L hL) b hL

end HigherLevelPredictionTestMatrix

end Schur

end CNNA.PillarA.Arithmetic
