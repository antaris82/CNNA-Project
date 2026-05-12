import CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive HigherLevelDiscriminantSearchStatus where
  | ar11DiscriminantSearchClosedByCertificate
  deriving DecidableEq, Repr

inductive HigherLevelFormalOutputStatus where
  | theoremCertificateOrExplicitObservationOnly
  deriving DecidableEq, Repr

inductive HigherLevelUncertifiedNumericsStatus where
  | uncertifiedNumericsExcludedFromFormalPath
  deriving DecidableEq, Repr

structure HigherLevelDiscriminantSearchLedger
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  outcomeRoute : HigherLevelOutcomeRoute B b hL z
  outcome : HigherLevelAR11Outcome
  outcome_eq_route : outcome = outcomeRoute.outcome
  searchStatus : HigherLevelDiscriminantSearchStatus
  searchStatus_eq :
    searchStatus =
      HigherLevelDiscriminantSearchStatus.ar11DiscriminantSearchClosedByCertificate
  formalOutputStatus : HigherLevelFormalOutputStatus
  formalOutputStatus_eq :
    formalOutputStatus = HigherLevelFormalOutputStatus.theoremCertificateOrExplicitObservationOnly
  uncertifiedNumericsStatus : HigherLevelUncertifiedNumericsStatus
  uncertifiedNumericsStatus_eq :
    uncertifiedNumericsStatus =
      HigherLevelUncertifiedNumericsStatus.uncertifiedNumericsExcludedFromFormalPath
  levelGreaterThanThree : 3 < L
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace HigherLevelDiscriminantSearchLedger

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

def fromCertificate
    (C : HigherLevelAR11Certificate B b hL z) :
    HigherLevelDiscriminantSearchLedger B b hL z :=
  let R := HigherLevelOutcomeRoute.fromCertificate C
  {
    outcomeRoute := R
    outcome := R.outcome
    outcome_eq_route := by
      rfl
    searchStatus := HigherLevelDiscriminantSearchStatus.ar11DiscriminantSearchClosedByCertificate
    searchStatus_eq := by
      rfl
    formalOutputStatus := HigherLevelFormalOutputStatus.theoremCertificateOrExplicitObservationOnly
    formalOutputStatus_eq := by
      rfl
    uncertifiedNumericsStatus :=
      HigherLevelUncertifiedNumericsStatus.uncertifiedNumericsExcludedFromFormalPath
    uncertifiedNumericsStatus_eq := by
      rfl
    levelGreaterThanThree := R.levelGreaterThanThree
    route := R.route
    noCutSpecCarrierClaim := R.noCutSpecCarrierClaim
  }

theorem search_status_closed
    (Ldg : HigherLevelDiscriminantSearchLedger B b hL z) :
    Ldg.searchStatus =
      HigherLevelDiscriminantSearchStatus.ar11DiscriminantSearchClosedByCertificate :=
  Ldg.searchStatus_eq

theorem formal_output_status
    (Ldg : HigherLevelDiscriminantSearchLedger B b hL z) :
    Ldg.formalOutputStatus = HigherLevelFormalOutputStatus.theoremCertificateOrExplicitObservationOnly :=
  Ldg.formalOutputStatus_eq

theorem uncertified_numerics_excluded
    (Ldg : HigherLevelDiscriminantSearchLedger B b hL z) :
    Ldg.uncertifiedNumericsStatus =
      HigherLevelUncertifiedNumericsStatus.uncertifiedNumericsExcludedFromFormalPath :=
  Ldg.uncertifiedNumericsStatus_eq

theorem outcome_three_way
    (Ldg : HigherLevelDiscriminantSearchLedger B b hL z) :
    Ldg.outcome = HigherLevelAR11Outcome.quadraticHeegnerHit ∨
      Ldg.outcome = HigherLevelAR11Outcome.quadraticNonHeegner ∨
        Ldg.outcome = HigherLevelAR11Outcome.irreducibleOrHigherDegree := by
  have hR := HigherLevelOutcomeRoute.outcome_three_way Ldg.outcomeRoute
  cases hR with
  | inl h =>
      exact Or.inl (Eq.trans Ldg.outcome_eq_route h)
  | inr hRest =>
      cases hRest with
      | inl h =>
          exact Or.inr (Or.inl (Eq.trans Ldg.outcome_eq_route h))
      | inr h =>
          exact Or.inr (Or.inr (Eq.trans Ldg.outcome_eq_route h))

theorem route_recursiveHistory
    (Ldg : HigherLevelDiscriminantSearchLedger B b hL z) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem noCutSpecCarrierClaim_at
    (Ldg : HigherLevelDiscriminantSearchLedger B b hL z)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim k

end HigherLevelDiscriminantSearchLedger

end Schur

namespace StrengtheningAR11

abbrev AR11DiscriminantSearchStatus := Schur.HigherLevelDiscriminantSearchStatus
abbrev AR11FormalOutputStatus := Schur.HigherLevelFormalOutputStatus
abbrev AR11UncertifiedNumericsStatus := Schur.HigherLevelUncertifiedNumericsStatus

abbrev AR11DiscriminantSearchLedger
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) :=
  Schur.HigherLevelDiscriminantSearchLedger B b hL z

def AR11DiscriminantSearchLedgerFromCertificate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (C : Schur.HigherLevelAR11Certificate B b hL z) :
    AR11DiscriminantSearchLedger B b hL z :=
  Schur.HigherLevelDiscriminantSearchLedger.fromCertificate C

theorem AR11DiscriminantSearchLedger_outcome_three_way
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (Ldg : AR11DiscriminantSearchLedger B b hL z) :
    Ldg.outcome = Schur.HigherLevelAR11Outcome.quadraticHeegnerHit ∨
      Ldg.outcome = Schur.HigherLevelAR11Outcome.quadraticNonHeegner ∨
        Ldg.outcome = Schur.HigherLevelAR11Outcome.irreducibleOrHigherDegree :=
  Schur.HigherLevelDiscriminantSearchLedger.outcome_three_way Ldg

end StrengtheningAR11

end CNNA.PillarA.Arithmetic
