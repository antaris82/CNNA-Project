import CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive HigherLevelAR11Outcome where
  | quadraticHeegnerHit
  | quadraticNonHeegner
  | irreducibleOrHigherDegree
  deriving DecidableEq, Repr

inductive HigherLevelHeegnerD where
  | d1
  | d2
  | d3
  | d7
  | d11
  | d19
  | d43
  | d67
  | d163
  deriving DecidableEq, Repr

namespace HigherLevelHeegnerD

def toNat : HigherLevelHeegnerD → Nat
  | d1 => 1
  | d2 => 2
  | d3 => 3
  | d7 => 7
  | d11 => 11
  | d19 => 19
  | d43 => 43
  | d67 => 67
  | d163 => 163

theorem toNat_positive (d : HigherLevelHeegnerD) : 0 < d.toNat := by
  cases d with
  | d1 => exact Nat.succ_pos 0
  | d2 => exact Nat.succ_pos 1
  | d3 => exact Nat.succ_pos 2
  | d7 => exact Nat.succ_pos 6
  | d11 => exact Nat.succ_pos 10
  | d19 => exact Nat.succ_pos 18
  | d43 => exact Nat.succ_pos 42
  | d67 => exact Nat.succ_pos 66
  | d163 => exact Nat.succ_pos 162

end HigherLevelHeegnerD

inductive HigherLevelFactorizationCertificateStatus where
  | factorizationCertificateProvided
  deriving DecidableEq, Repr

inductive HigherLevelMinimalPolynomialCertificateStatus where
  | minimalPolynomialDegreeCertificateProvided
  deriving DecidableEq, Repr

inductive HigherLevelDiscriminantCertificateStatus where
  | discriminantCertificateProvided
  deriving DecidableEq, Repr

inductive HigherLevelFundamentalBridgeStatus where
  | schurToFundamentalDiscriminantCertificateProvided
  | deferredToAR12DiscriminantConvention
  deriving DecidableEq, Repr

inductive HigherLevelHeegnerListCertificateStatus where
  | positiveDInHeegnerListCertified
  | positiveDNotInHeegnerListCertified
  | notApplicableForNonQuadraticOutcome
  deriving DecidableEq, Repr

inductive HigherLevelNoNumericalShortcutStatus where
  | noUncertifiedNumericsNoPredictionRowInput
  deriving DecidableEq, Repr

inductive HigherLevelNonQuadraticKind where
  | irreducibleOverQ
  | higherDegreeFactor
  deriving DecidableEq, Repr

structure HigherLevelAR11SearchBase
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  predictionLedger : HigherLevelPredictionLedger B b hL
  predictionLedger_eq : predictionLedger = HigherLevelPredictionLedger.fromBoundarySource B b hL
  charpolyLedger : OperativeCharpolyLedger source L z
  charpolyLedger_eq : charpolyLedger = OperativeCharpolyLedger.fromBoundarySource B z
  levelGreaterThanThree : 3 < L
  recurrenceClosed :
    charpolyLedger.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  charpolyClosed :
    charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  numeratorAgreement :
    ∀ k : BoundarySource.LevelHistoryIndex L,
      charpolyLedger.profile.matrix k k =
        charpolyLedger.recurrenceLedger.recursiveSource.numerator k
  noFreeCharpolyAssumptions :
    charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  predictionOpen :
    predictionLedger.row.predictionStatus = HigherLevelPredictionStatus.openPrediction
  predictionNoDownstreamInput :
    predictionLedger.row.downstreamDisciplineStatus =
      HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16
  predictionNoAR11CertificateBeforeSearch :
    predictionLedger.row.ar11CertificateReferenceStatus =
      HigherLevelAR11CertificateReferenceStatus.noAR11CertificateYet
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace HigherLevelAR11SearchBase

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) :
    HigherLevelAR11SearchBase B b hL z where
  predictionLedger := HigherLevelPredictionLedger.fromBoundarySource B b hL
  predictionLedger_eq := by
    rfl
  charpolyLedger := OperativeCharpolyLedger.fromBoundarySource B z
  charpolyLedger_eq := by
    rfl
  levelGreaterThanThree := hL
  recurrenceClosed := by
    rfl
  charpolyClosed := by
    rfl
  numeratorAgreement := by
    intro k
    exact OperativeCharpolyLedger.diagonal_agrees_with_schurNumerator
      (OperativeCharpolyLedger.fromBoundarySource B z) k
  noFreeCharpolyAssumptions := by
    rfl
  predictionOpen := HigherLevelPredictionLedger.row_status_open
    (HigherLevelPredictionLedger.fromBoundarySource B b hL)
  predictionNoDownstreamInput := HigherLevelPredictionLedger.row_no_downstream_input
    (HigherLevelPredictionLedger.fromBoundarySource B b hL)
  predictionNoAR11CertificateBeforeSearch := HigherLevelPredictionLedger.row_no_ar11_certificate
    (HigherLevelPredictionLedger.fromBoundarySource B b hL)
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem charpoly_status_closed
    (S : HigherLevelAR11SearchBase B b hL z) :
    S.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  S.charpolyClosed

theorem recurrence_status_closed
    (S : HigherLevelAR11SearchBase B b hL z) :
    S.charpolyLedger.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed :=
  S.recurrenceClosed

theorem prediction_is_open_before_certificate
    (S : HigherLevelAR11SearchBase B b hL z) :
    S.predictionLedger.row.predictionStatus = HigherLevelPredictionStatus.openPrediction :=
  S.predictionOpen

theorem prediction_not_downstream_input
    (S : HigherLevelAR11SearchBase B b hL z) :
    S.predictionLedger.row.downstreamDisciplineStatus =
      HigherLevelDownstreamDisciplineStatus.noPredictionRowMayServeAsInputForAR11ToAR16 :=
  S.predictionNoDownstreamInput

theorem no_free_charpoly_assumptions
    (S : HigherLevelAR11SearchBase B b hL z) :
    S.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  S.noFreeCharpolyAssumptions

theorem route_recursiveHistory
    (S : HigherLevelAR11SearchBase B b hL z) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  S.route

theorem noCutSpecCarrierClaim_at
    (S : HigherLevelAR11SearchBase B b hL z)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  S.noCutSpecCarrierClaim k

end HigherLevelAR11SearchBase

structure HigherLevelQuadraticHeegnerCertificate
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  base : HigherLevelAR11SearchBase B b hL z
  factorDegree : Nat
  factorDegree_eq_two : factorDegree = 2
  minimalPolynomialDegree : Nat
  minimalPolynomialDegree_eq_two : minimalPolynomialDegree = 2
  schurDiscriminant : ℤ
  convertedPositiveD : Nat
  heegnerD : HigherLevelHeegnerD
  convertedPositiveD_eq_heegnerD : convertedPositiveD = heegnerD.toNat
  factorizationStatus : HigherLevelFactorizationCertificateStatus
  factorizationStatus_eq :
    factorizationStatus =
      HigherLevelFactorizationCertificateStatus.factorizationCertificateProvided
  minimalPolynomialStatus : HigherLevelMinimalPolynomialCertificateStatus
  minimalPolynomialStatus_eq :
    minimalPolynomialStatus =
      HigherLevelMinimalPolynomialCertificateStatus.minimalPolynomialDegreeCertificateProvided
  discriminantStatus : HigherLevelDiscriminantCertificateStatus
  discriminantStatus_eq :
    discriminantStatus =
      HigherLevelDiscriminantCertificateStatus.discriminantCertificateProvided
  fundamentalBridgeStatus : HigherLevelFundamentalBridgeStatus
  fundamentalBridgeStatus_eq :
    fundamentalBridgeStatus =
      HigherLevelFundamentalBridgeStatus.schurToFundamentalDiscriminantCertificateProvided
  heegnerListStatus : HigherLevelHeegnerListCertificateStatus
  heegnerListStatus_eq :
    heegnerListStatus = HigherLevelHeegnerListCertificateStatus.positiveDInHeegnerListCertified
  noNumericalShortcutStatus : HigherLevelNoNumericalShortcutStatus
  noNumericalShortcutStatus_eq :
    noNumericalShortcutStatus =
      HigherLevelNoNumericalShortcutStatus.noUncertifiedNumericsNoPredictionRowInput
  outcome : HigherLevelAR11Outcome
  outcome_eq : outcome = HigherLevelAR11Outcome.quadraticHeegnerHit

namespace HigherLevelQuadraticHeegnerCertificate

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

theorem outcome_is_quadratic_heegner
    (C : HigherLevelQuadraticHeegnerCertificate B b hL z) :
    C.outcome = HigherLevelAR11Outcome.quadraticHeegnerHit :=
  C.outcome_eq

theorem degree_is_two
    (C : HigherLevelQuadraticHeegnerCertificate B b hL z) :
    C.factorDegree = 2 :=
  C.factorDegree_eq_two

theorem positiveD_from_heegner_witness
    (C : HigherLevelQuadraticHeegnerCertificate B b hL z) :
    C.convertedPositiveD = C.heegnerD.toNat :=
  C.convertedPositiveD_eq_heegnerD

theorem charpoly_closed
    (C : HigherLevelQuadraticHeegnerCertificate B b hL z) :
    C.base.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  C.base.charpolyClosed

end HigherLevelQuadraticHeegnerCertificate

structure HigherLevelQuadraticNonHeegnerCertificate
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  base : HigherLevelAR11SearchBase B b hL z
  factorDegree : Nat
  factorDegree_eq_two : factorDegree = 2
  minimalPolynomialDegree : Nat
  minimalPolynomialDegree_eq_two : minimalPolynomialDegree = 2
  schurDiscriminant : ℤ
  convertedPositiveD : Nat
  factorizationStatus : HigherLevelFactorizationCertificateStatus
  factorizationStatus_eq :
    factorizationStatus =
      HigherLevelFactorizationCertificateStatus.factorizationCertificateProvided
  minimalPolynomialStatus : HigherLevelMinimalPolynomialCertificateStatus
  minimalPolynomialStatus_eq :
    minimalPolynomialStatus =
      HigherLevelMinimalPolynomialCertificateStatus.minimalPolynomialDegreeCertificateProvided
  discriminantStatus : HigherLevelDiscriminantCertificateStatus
  discriminantStatus_eq :
    discriminantStatus =
      HigherLevelDiscriminantCertificateStatus.discriminantCertificateProvided
  fundamentalBridgeStatus : HigherLevelFundamentalBridgeStatus
  fundamentalBridgeStatus_eq :
    fundamentalBridgeStatus =
      HigherLevelFundamentalBridgeStatus.schurToFundamentalDiscriminantCertificateProvided
  heegnerListStatus : HigherLevelHeegnerListCertificateStatus
  heegnerListStatus_eq :
    heegnerListStatus = HigherLevelHeegnerListCertificateStatus.positiveDNotInHeegnerListCertified
  noNumericalShortcutStatus : HigherLevelNoNumericalShortcutStatus
  noNumericalShortcutStatus_eq :
    noNumericalShortcutStatus =
      HigherLevelNoNumericalShortcutStatus.noUncertifiedNumericsNoPredictionRowInput
  outcome : HigherLevelAR11Outcome
  outcome_eq : outcome = HigherLevelAR11Outcome.quadraticNonHeegner

namespace HigherLevelQuadraticNonHeegnerCertificate

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

theorem outcome_is_quadratic_non_heegner
    (C : HigherLevelQuadraticNonHeegnerCertificate B b hL z) :
    C.outcome = HigherLevelAR11Outcome.quadraticNonHeegner :=
  C.outcome_eq

theorem degree_is_two
    (C : HigherLevelQuadraticNonHeegnerCertificate B b hL z) :
    C.factorDegree = 2 :=
  C.factorDegree_eq_two

theorem charpoly_closed
    (C : HigherLevelQuadraticNonHeegnerCertificate B b hL z) :
    C.base.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  C.base.charpolyClosed

end HigherLevelQuadraticNonHeegnerCertificate

structure HigherLevelIrreducibleOrHigherDegreeCertificate
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  base : HigherLevelAR11SearchBase B b hL z
  nonQuadraticKind : HigherLevelNonQuadraticKind
  factorDegree : Nat
  minimalPolynomialDegree : Nat
  schurDiscriminant : Option ℤ
  factorizationStatus : HigherLevelFactorizationCertificateStatus
  factorizationStatus_eq :
    factorizationStatus =
      HigherLevelFactorizationCertificateStatus.factorizationCertificateProvided
  minimalPolynomialStatus : HigherLevelMinimalPolynomialCertificateStatus
  minimalPolynomialStatus_eq :
    minimalPolynomialStatus =
      HigherLevelMinimalPolynomialCertificateStatus.minimalPolynomialDegreeCertificateProvided
  discriminantStatus : HigherLevelDiscriminantCertificateStatus
  discriminantStatus_eq :
    discriminantStatus =
      HigherLevelDiscriminantCertificateStatus.discriminantCertificateProvided
  fundamentalBridgeStatus : HigherLevelFundamentalBridgeStatus
  fundamentalBridgeStatus_eq :
    fundamentalBridgeStatus =
      HigherLevelFundamentalBridgeStatus.deferredToAR12DiscriminantConvention
  heegnerListStatus : HigherLevelHeegnerListCertificateStatus
  heegnerListStatus_eq :
    heegnerListStatus = HigherLevelHeegnerListCertificateStatus.notApplicableForNonQuadraticOutcome
  noNumericalShortcutStatus : HigherLevelNoNumericalShortcutStatus
  noNumericalShortcutStatus_eq :
    noNumericalShortcutStatus =
      HigherLevelNoNumericalShortcutStatus.noUncertifiedNumericsNoPredictionRowInput
  outcome : HigherLevelAR11Outcome
  outcome_eq : outcome = HigherLevelAR11Outcome.irreducibleOrHigherDegree

namespace HigherLevelIrreducibleOrHigherDegreeCertificate

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

theorem outcome_is_irreducible_or_higher_degree
    (C : HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    C.outcome = HigherLevelAR11Outcome.irreducibleOrHigherDegree :=
  C.outcome_eq

theorem heegner_not_applicable
    (C : HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    C.heegnerListStatus = HigherLevelHeegnerListCertificateStatus.notApplicableForNonQuadraticOutcome :=
  C.heegnerListStatus_eq

theorem charpoly_closed
    (C : HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    C.base.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  C.base.charpolyClosed

end HigherLevelIrreducibleOrHigherDegreeCertificate

structure HigherLevelAR11Certificate
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  quadraticHeegnerPayload : Option (HigherLevelQuadraticHeegnerCertificate B b hL z)
  quadraticNonHeegnerPayload : Option (HigherLevelQuadraticNonHeegnerCertificate B b hL z)
  irreducibleOrHigherDegreePayload :
    Option (HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z)
  outcome : HigherLevelAR11Outcome

namespace HigherLevelAR11Certificate

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

def quadraticHeegner
    (C : HigherLevelQuadraticHeegnerCertificate B b hL z) :
    HigherLevelAR11Certificate B b hL z where
  quadraticHeegnerPayload := some C
  quadraticNonHeegnerPayload := none
  irreducibleOrHigherDegreePayload := none
  outcome := HigherLevelAR11Outcome.quadraticHeegnerHit

def quadraticNonHeegner
    (C : HigherLevelQuadraticNonHeegnerCertificate B b hL z) :
    HigherLevelAR11Certificate B b hL z where
  quadraticHeegnerPayload := none
  quadraticNonHeegnerPayload := some C
  irreducibleOrHigherDegreePayload := none
  outcome := HigherLevelAR11Outcome.quadraticNonHeegner

def irreducibleOrHigherDegree
    (C : HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    HigherLevelAR11Certificate B b hL z where
  quadraticHeegnerPayload := none
  quadraticNonHeegnerPayload := none
  irreducibleOrHigherDegreePayload := some C
  outcome := HigherLevelAR11Outcome.irreducibleOrHigherDegree

theorem outcome_three_way
    (C : HigherLevelAR11Certificate B b hL z) :
    C.outcome = HigherLevelAR11Outcome.quadraticHeegnerHit ∨
      C.outcome = HigherLevelAR11Outcome.quadraticNonHeegner ∨
        C.outcome = HigherLevelAR11Outcome.irreducibleOrHigherDegree := by
  cases C.outcome with
  | quadraticHeegnerHit =>
      exact Or.inl rfl
  | quadraticNonHeegner =>
      exact Or.inr (Or.inl rfl)
  | irreducibleOrHigherDegree =>
      exact Or.inr (Or.inr rfl)

end HigherLevelAR11Certificate

end Schur

namespace StrengtheningAR11

abbrev AR11Outcome := Schur.HigherLevelAR11Outcome
abbrev AR11HeegnerD := Schur.HigherLevelHeegnerD
abbrev AR11FactorizationCertificateStatus :=
  Schur.HigherLevelFactorizationCertificateStatus
abbrev AR11MinimalPolynomialCertificateStatus :=
  Schur.HigherLevelMinimalPolynomialCertificateStatus
abbrev AR11DiscriminantCertificateStatus :=
  Schur.HigherLevelDiscriminantCertificateStatus
abbrev AR11FundamentalBridgeStatus :=
  Schur.HigherLevelFundamentalBridgeStatus
abbrev AR11HeegnerListCertificateStatus :=
  Schur.HigherLevelHeegnerListCertificateStatus
abbrev AR11NoNumericalShortcutStatus :=
  Schur.HigherLevelNoNumericalShortcutStatus
abbrev AR11NonQuadraticKind := Schur.HigherLevelNonQuadraticKind

abbrev AR11SearchBase
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) :=
  Schur.HigherLevelAR11SearchBase B b hL z

abbrev AR11Certificate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) :=
  Schur.HigherLevelAR11Certificate B b hL z

def AR11SearchBaseFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) :
    AR11SearchBase B b hL z :=
  Schur.HigherLevelAR11SearchBase.fromBoundarySource B b hL z

theorem AR11SearchBase_charpoly_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (S : AR11SearchBase B b hL z) :
    S.charpolyLedger.profile.computationStatus =
      Schur.OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  Schur.HigherLevelAR11SearchBase.charpoly_status_closed S

theorem AR11Certificate_outcome_three_way
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (C : AR11Certificate B b hL z) :
    Schur.HigherLevelAR11Certificate.outcome C = Schur.HigherLevelAR11Outcome.quadraticHeegnerHit ∨
      Schur.HigherLevelAR11Certificate.outcome C = Schur.HigherLevelAR11Outcome.quadraticNonHeegner ∨
        Schur.HigherLevelAR11Certificate.outcome C =
          Schur.HigherLevelAR11Outcome.irreducibleOrHigherDegree :=
  Schur.HigherLevelAR11Certificate.outcome_three_way C

end StrengtheningAR11

end CNNA.PillarA.Arithmetic
