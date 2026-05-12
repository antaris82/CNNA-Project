import CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive HigherLevelOutcomeRouterStatus where
  | ar11OutcomeRouterClosed
  deriving DecidableEq, Repr

inductive HigherLevelOutcomeExclusivityStatus where
  | exactlyOneCertificateConstructorSelected
  deriving DecidableEq, Repr

inductive HigherLevelAR12ForwardingStatus where
  | quadraticOnlyAfterCertificate
  | blockedForIrreducibleOrHigherDegree
  deriving DecidableEq, Repr

structure HigherLevelOutcomeRoute
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : SpectralParameter) where
  certificate : HigherLevelAR11Certificate B b hL z
  outcome : HigherLevelAR11Outcome
  outcome_eq_certificate : outcome = HigherLevelAR11Certificate.outcome certificate
  routerStatus : HigherLevelOutcomeRouterStatus
  routerStatus_eq : routerStatus = HigherLevelOutcomeRouterStatus.ar11OutcomeRouterClosed
  exclusivityStatus : HigherLevelOutcomeExclusivityStatus
  exclusivityStatus_eq :
    exclusivityStatus = HigherLevelOutcomeExclusivityStatus.exactlyOneCertificateConstructorSelected
  levelGreaterThanThree : 3 < L
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace HigherLevelOutcomeRoute

variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : SpectralParameter}

def fromCertificate
    (C : HigherLevelAR11Certificate B b hL z) :
    HigherLevelOutcomeRoute B b hL z where
  certificate := C
  outcome := HigherLevelAR11Certificate.outcome C
  outcome_eq_certificate := by
    rfl
  routerStatus := HigherLevelOutcomeRouterStatus.ar11OutcomeRouterClosed
  routerStatus_eq := by
    rfl
  exclusivityStatus := HigherLevelOutcomeExclusivityStatus.exactlyOneCertificateConstructorSelected
  exclusivityStatus_eq := by
    rfl
  levelGreaterThanThree := hL
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

def forwardingStatus (R : HigherLevelOutcomeRoute B b hL z) :
    HigherLevelAR12ForwardingStatus :=
  match R.outcome with
  | HigherLevelAR11Outcome.quadraticHeegnerHit =>
      HigherLevelAR12ForwardingStatus.quadraticOnlyAfterCertificate
  | HigherLevelAR11Outcome.quadraticNonHeegner =>
      HigherLevelAR12ForwardingStatus.quadraticOnlyAfterCertificate
  | HigherLevelAR11Outcome.irreducibleOrHigherDegree =>
      HigherLevelAR12ForwardingStatus.blockedForIrreducibleOrHigherDegree

theorem router_status_closed
    (R : HigherLevelOutcomeRoute B b hL z) :
    R.routerStatus = HigherLevelOutcomeRouterStatus.ar11OutcomeRouterClosed :=
  R.routerStatus_eq

theorem exclusivity_status_closed
    (R : HigherLevelOutcomeRoute B b hL z) :
    R.exclusivityStatus = HigherLevelOutcomeExclusivityStatus.exactlyOneCertificateConstructorSelected :=
  R.exclusivityStatus_eq

theorem outcome_three_way
    (R : HigherLevelOutcomeRoute B b hL z) :
    R.outcome = HigherLevelAR11Outcome.quadraticHeegnerHit ∨
      R.outcome = HigherLevelAR11Outcome.quadraticNonHeegner ∨
        R.outcome = HigherLevelAR11Outcome.irreducibleOrHigherDegree := by
  have hC := HigherLevelAR11Certificate.outcome_three_way R.certificate
  cases hC with
  | inl h =>
      exact Or.inl (Eq.trans R.outcome_eq_certificate h)
  | inr hRest =>
      cases hRest with
      | inl h =>
          exact Or.inr (Or.inl (Eq.trans R.outcome_eq_certificate h))
      | inr h =>
          exact Or.inr (Or.inr (Eq.trans R.outcome_eq_certificate h))

theorem route_recursiveHistory
    (R : HigherLevelOutcomeRoute B b hL z) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  R.route

theorem noCutSpecCarrierClaim_at
    (R : HigherLevelOutcomeRoute B b hL z)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  R.noCutSpecCarrierClaim k

end HigherLevelOutcomeRoute

end Schur

namespace StrengtheningAR11

abbrev AR11OutcomeRouterStatus := Schur.HigherLevelOutcomeRouterStatus
abbrev AR11OutcomeExclusivityStatus := Schur.HigherLevelOutcomeExclusivityStatus
abbrev AR11AR12ForwardingStatus := Schur.HigherLevelAR12ForwardingStatus

abbrev AR11OutcomeRoute
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) :=
  Schur.HigherLevelOutcomeRoute B b hL z

def AR11OutcomeRouteFromCertificate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (C : Schur.HigherLevelAR11Certificate B b hL z) :
    AR11OutcomeRoute B b hL z :=
  Schur.HigherLevelOutcomeRoute.fromCertificate C

theorem AR11OutcomeRoute_three_way
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (R : AR11OutcomeRoute B b hL z) :
    R.outcome = Schur.HigherLevelAR11Outcome.quadraticHeegnerHit ∨
      R.outcome = Schur.HigherLevelAR11Outcome.quadraticNonHeegner ∨
        R.outcome = Schur.HigherLevelAR11Outcome.irreducibleOrHigherDegree :=
  Schur.HigherLevelOutcomeRoute.outcome_three_way R

end StrengtheningAR11

end CNNA.PillarA.Arithmetic
