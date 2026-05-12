import CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure RecursiveLevelHistoryRoute
    (source : ArithmeticSource Cell T) (L : Nat) where
  carrier : RecursiveLevelHistoryCarrier source L
  adapter : MultiSchurToLevelHistoryAdapter source L carrier

namespace RecursiveLevelHistoryRoute

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromPackage
    (carrier : RecursiveLevelHistoryCarrier source L)
    (package : LevelHistoryMatrixPackage source L carrier) :
    RecursiveLevelHistoryRoute source L where
  carrier := carrier
  adapter := {
    package := package
    sourceMultiSchur_eq := by
      rfl
    sourceDtn_eq := by
      rfl
    sourceGeneralizedDtN_eq := by
      rfl
    adapterOnlyBeforeEqualityLemmas := True.intro }

def fromAdapter
    (carrier : RecursiveLevelHistoryCarrier source L)
    (adapter : MultiSchurToLevelHistoryAdapter source L carrier) :
    RecursiveLevelHistoryRoute source L where
  carrier := carrier
  adapter := adapter

def matrixPackage (R : RecursiveLevelHistoryRoute source L) :
    LevelHistoryMatrixPackage source L R.carrier :=
  R.adapter.package

def matrix (R : RecursiveLevelHistoryRoute source L) :
    LevelHistoryMatrix L :=
  R.matrixPackage.matrix

theorem matrix_from_source
    (R : RecursiveLevelHistoryRoute source L) :
    MatrixDerivedFrom source L R.carrier R.matrix :=
  R.matrixPackage.matrix_from_source

theorem adapter_dtnAnchor
    (R : RecursiveLevelHistoryRoute source L) :
    source.dtn = source.multiSchur.binary :=
  R.adapter.sourceDtn_eq

theorem adapter_generalizedDtNAnchor
    (R : RecursiveLevelHistoryRoute source L) :
    source.generalizedDtN = source.multiSchur.generalized :=
  R.adapter.sourceGeneralizedDtN_eq

theorem adapter_multiSchurAnchor
    (R : RecursiveLevelHistoryRoute source L) :
    source.coupling = source.multiSchur :=
  R.adapter.sourceMultiSchur_eq

theorem noCutSpecCarrierClaim_at
    (R : RecursiveLevelHistoryRoute source L)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  R.matrixPackage.matrix_from_source.noCutSpecCarrierClaim k

def provenance (R : RecursiveLevelHistoryRoute source L) :
    BoundarySourceProvenance source L where
  carrier := R.carrier
  matrixPackage := R.matrixPackage
  adapter := R.adapter
  adapter_package_eq := by
    rfl
  route := BoundarySourceRoute.recursiveHistory
  route_eq_recursiveHistory := by
    rfl
  signatureDecision := RecursiveHistorySignatureDecision.closed
  signatureDecision_closed := by
    rfl

def interface (R : RecursiveLevelHistoryRoute source L) :
    BoundarySourceInterface source L where
  index := LevelHistoryIndex L
  indexEquiv := Equiv.refl (LevelHistoryIndex L)
  matrix := R.matrix
  provenance := R.provenance
  route := BoundarySourceRoute.recursiveHistory
  route_eq_provenance := by
    rfl
  matrix_eq_transport := by
    funext i j
    rfl

theorem interface_route
    (R : RecursiveLevelHistoryRoute source L) :
    R.interface.route = BoundarySourceRoute.recursiveHistory := by
  rfl

theorem interface_indexEquiv_apply
    (R : RecursiveLevelHistoryRoute source L) (k : R.interface.index) :
    R.interface.indexEquiv k = k := by
  rfl

theorem interface_matrix_eq_route_matrix
    (R : RecursiveLevelHistoryRoute source L) :
    R.interface.matrix = R.matrix := by
  rfl

theorem interface_matrix_is_transport
    (R : RecursiveLevelHistoryRoute source L) :
    R.interface.matrix =
      transportLevelHistoryMatrix R.interface.indexEquiv
        R.interface.provenance.matrixPackage.matrix :=
  R.interface.matrix_eq_transport

theorem interface_decision_closed
    (R : RecursiveLevelHistoryRoute source L) :
    R.interface.provenance.signatureDecision.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem interface_noCutSpecCarrierClaim_at
    (R : RecursiveLevelHistoryRoute source L)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  R.noCutSpecCarrierClaim_at k

end RecursiveLevelHistoryRoute

structure RecursiveLevelHistoryRouteLedger
    (source : ArithmeticSource Cell T) (L : Nat) where
  route : RecursiveLevelHistoryRoute source L
  interfaceOnlyExport : BoundarySourceInterface source L
  interfaceOnlyExport_eq : interfaceOnlyExport = route.interface
  route_eq_recursiveHistory : interfaceOnlyExport.route = BoundarySourceRoute.recursiveHistory
  signatureClosed :
    interfaceOnlyExport.provenance.signatureDecision.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed
  indexIsLevelHistoryIndex : interfaceOnlyExport.index = LevelHistoryIndex L
  matrixDerivedFromSource :
    MatrixDerivedFrom source L route.carrier route.matrix
  noCutSpecCarrierClaim :
    ∀ _ : LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace RecursiveLevelHistoryRouteLedger

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromRoute (R : RecursiveLevelHistoryRoute source L) :
    RecursiveLevelHistoryRouteLedger source L where
  route := R
  interfaceOnlyExport := R.interface
  interfaceOnlyExport_eq := by
    rfl
  route_eq_recursiveHistory := by
    rfl
  signatureClosed := by
    rfl
  indexIsLevelHistoryIndex := by
    rfl
  matrixDerivedFromSource := R.matrix_from_source
  noCutSpecCarrierClaim := by
    intro k
    exact R.noCutSpecCarrierClaim_at k

theorem fromRoute_route
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRoute R).interfaceOnlyExport.route = BoundarySourceRoute.recursiveHistory := by
  rfl

theorem fromRoute_signatureClosed
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRoute R).interfaceOnlyExport.provenance.signatureDecision.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem fromRoute_matrixDerivedFromSource
    (R : RecursiveLevelHistoryRoute source L) :
    MatrixDerivedFrom source L (fromRoute R).route.carrier (fromRoute R).route.matrix :=
  (fromRoute R).matrixDerivedFromSource

end RecursiveLevelHistoryRouteLedger

end BoundarySource

namespace StrengtheningAR2b2

abbrev AR2b2RecursiveLevelHistoryRouteOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.RecursiveLevelHistoryRoute (Cell := Cell) (T := T) source L

abbrev AR2b2RecursiveLevelHistoryRouteLedgerOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.RecursiveLevelHistoryRouteLedger (Cell := Cell) (T := T) source L

def ar2b2RecursiveLevelHistoryRouteFromPackage
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (carrier : BoundarySource.RecursiveLevelHistoryCarrier source L)
    (package : BoundarySource.LevelHistoryMatrixPackage source L carrier) :
    AR2b2RecursiveLevelHistoryRouteOf source L :=
  BoundarySource.RecursiveLevelHistoryRoute.fromPackage carrier package

def ar2b2RecursiveLevelHistoryInterface
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    BoundarySource.BoundarySourceInterface source L :=
  R.interface

def ar2b2RecursiveLevelHistoryRouteLedger
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    AR2b2RecursiveLevelHistoryRouteLedgerOf source L :=
  BoundarySource.RecursiveLevelHistoryRouteLedger.fromRoute R

theorem ar2b2RecursiveLevelHistoryInterface_route
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    (ar2b2RecursiveLevelHistoryInterface R).route =
      BoundarySource.BoundarySourceRoute.recursiveHistory := by
  rfl

theorem ar2b2RecursiveLevelHistoryInterface_decisionClosed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    (ar2b2RecursiveLevelHistoryInterface R).provenance.signatureDecision.status =
      BoundarySource.RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

end StrengtheningAR2b2

end CNNA.PillarA.Arithmetic
