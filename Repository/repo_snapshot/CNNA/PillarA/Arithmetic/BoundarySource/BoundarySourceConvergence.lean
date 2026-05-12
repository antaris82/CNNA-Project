import CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute
import CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

inductive BoundarySourceConvergenceStatus where
  | unavailable
  | obstruction
  | partialWitness
  | recursiveWitness
  | generatedRecursiveCompatibility
  | generatedRecursiveObstruction
  deriving DecidableEq, Repr

inductive BoundarySourceConsumptionPolicy where
  | boundarySourceOnly
  deriving DecidableEq, Repr

structure BoundarySourceContributions
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySourceInterface source L) where
  dtnContribution : source.dtn = source.multiSchur.binary
  generalizedDtNContribution : source.generalizedDtN = source.multiSchur.generalized
  schurContribution : source.coupling = source.multiSchur
  adapterPackage_eq_matrixPackage : B.provenance.adapter.package = B.provenance.matrixPackage
  matrixDerivedFromSource :
    MatrixDerivedFrom source L B.provenance.carrier B.provenance.matrixPackage.matrix

structure BoundarySourceNoFreeBoundaryData
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySourceInterface source L) where
  carrierDecision :
    B.provenance.signatureDecision.carrier = CarrierTypeDecision.levelHistoryIndex
  aggregationDecision :
    B.provenance.signatureDecision.aggregation =
      AggregationDecision.sourceWitnessToProofCarryingMatrix
  interfaceExportDecision :
    B.provenance.signatureDecision.interfaceExport =
      InterfaceExportDecision.boundarySourceInterfaceOnly
  routeDecision : B.route = BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

structure BoundarySourceSurface
    (source : ArithmeticSource Cell T) (L : Nat) where
  interface : BoundarySourceInterface source L
  carrier : RecursiveLevelHistoryCarrier source L
  carrier_eq_interface : carrier = interface.provenance.carrier
  indexEmbedding : interface.index ≃ LevelHistoryIndex L
  indexEmbedding_eq_interface : indexEmbedding = interface.indexEquiv
  contributions : BoundarySourceContributions interface
  noFreeBoundaryData : BoundarySourceNoFreeBoundaryData interface
  consumptionPolicy : BoundarySourceConsumptionPolicy
  consumptionPolicy_interfaceOnly :
    consumptionPolicy = BoundarySourceConsumptionPolicy.boundarySourceOnly

namespace BoundarySourceContributions

variable {source : ArithmeticSource Cell T} {L : Nat}


def fromInterface (B : BoundarySourceInterface source L) :
    BoundarySourceContributions B where
  dtnContribution := B.provenance.adapter.sourceDtn_eq
  generalizedDtNContribution := B.provenance.adapter.sourceGeneralizedDtN_eq
  schurContribution := B.provenance.adapter.sourceMultiSchur_eq
  adapterPackage_eq_matrixPackage := B.provenance.adapter_package_eq
  matrixDerivedFromSource := B.provenance.matrixPackage.matrix_from_source

theorem dtnContribution_eq
    {B : BoundarySourceInterface source L}
    (C : BoundarySourceContributions B) :
    source.dtn = source.multiSchur.binary :=
  C.dtnContribution

theorem generalizedDtNContribution_eq
    {B : BoundarySourceInterface source L}
    (C : BoundarySourceContributions B) :
    source.generalizedDtN = source.multiSchur.generalized :=
  C.generalizedDtNContribution

theorem schurContribution_eq
    {B : BoundarySourceInterface source L}
    (C : BoundarySourceContributions B) :
    source.coupling = source.multiSchur :=
  C.schurContribution

theorem matrixDerivedFromSource_proof
    {B : BoundarySourceInterface source L}
    (C : BoundarySourceContributions B) :
    MatrixDerivedFrom source L B.provenance.carrier B.provenance.matrixPackage.matrix :=
  C.matrixDerivedFromSource

end BoundarySourceContributions

namespace BoundarySourceNoFreeBoundaryData

variable {source : ArithmeticSource Cell T} {L : Nat}

theorem carrierDecision_levelHistory
    {B : BoundarySourceInterface source L}
    (N : BoundarySourceNoFreeBoundaryData B) :
    B.provenance.signatureDecision.carrier = CarrierTypeDecision.levelHistoryIndex :=
  N.carrierDecision

theorem aggregationDecision_sourceWitnessToMatrix
    {B : BoundarySourceInterface source L}
    (N : BoundarySourceNoFreeBoundaryData B) :
    B.provenance.signatureDecision.aggregation =
      AggregationDecision.sourceWitnessToProofCarryingMatrix :=
  N.aggregationDecision

theorem interfaceExportDecision_interfaceOnly
    {B : BoundarySourceInterface source L}
    (N : BoundarySourceNoFreeBoundaryData B) :
    B.provenance.signatureDecision.interfaceExport =
      InterfaceExportDecision.boundarySourceInterfaceOnly :=
  N.interfaceExportDecision

theorem routeDecision_recursiveHistory
    {B : BoundarySourceInterface source L}
    (N : BoundarySourceNoFreeBoundaryData B) :
    B.route = BoundarySourceRoute.recursiveHistory :=
  N.routeDecision

theorem noCutSpecCarrierClaim_at
    {B : BoundarySourceInterface source L}
    (N : BoundarySourceNoFreeBoundaryData B) (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  N.noCutSpecCarrierClaim k

end BoundarySourceNoFreeBoundaryData

namespace BoundarySourceSurface

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromRecursiveRoute (R : RecursiveLevelHistoryRoute source L) :
    BoundarySourceSurface source L where
  interface := R.interface
  carrier := R.carrier
  carrier_eq_interface := by
    rfl
  indexEmbedding := R.interface.indexEquiv
  indexEmbedding_eq_interface := by
    rfl
  contributions := BoundarySourceContributions.fromInterface R.interface
  noFreeBoundaryData := {
    carrierDecision := by
      rfl
    aggregationDecision := by
      rfl
    interfaceExportDecision := by
      rfl
    routeDecision := by
      rfl
    noCutSpecCarrierClaim := by
      intro k
      exact R.noCutSpecCarrierClaim_at k }
  consumptionPolicy := BoundarySourceConsumptionPolicy.boundarySourceOnly
  consumptionPolicy_interfaceOnly := by
    rfl

theorem route_recursiveHistory
    (B : BoundarySourceSurface source L) :
    B.interface.route = BoundarySourceRoute.recursiveHistory :=
  B.noFreeBoundaryData.routeDecision

theorem consumptionPolicy_is_interfaceOnly
    (B : BoundarySourceSurface source L) :
    B.consumptionPolicy = BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  B.consumptionPolicy_interfaceOnly

theorem carrierDecision_levelHistory
    (B : BoundarySourceSurface source L) :
    B.interface.provenance.signatureDecision.carrier =
      CarrierTypeDecision.levelHistoryIndex :=
  B.noFreeBoundaryData.carrierDecision

theorem aggregationDecision_sourceWitnessToMatrix
    (B : BoundarySourceSurface source L) :
    B.interface.provenance.signatureDecision.aggregation =
      AggregationDecision.sourceWitnessToProofCarryingMatrix :=
  B.noFreeBoundaryData.aggregationDecision

theorem interfaceExportDecision_interfaceOnly
    (B : BoundarySourceSurface source L) :
    B.interface.provenance.signatureDecision.interfaceExport =
      InterfaceExportDecision.boundarySourceInterfaceOnly :=
  B.noFreeBoundaryData.interfaceExportDecision

theorem dtnContribution_eq
    (B : BoundarySourceSurface source L) :
    source.dtn = source.multiSchur.binary :=
  B.contributions.dtnContribution

theorem generalizedDtNContribution_eq
    (B : BoundarySourceSurface source L) :
    source.generalizedDtN = source.multiSchur.generalized :=
  B.contributions.generalizedDtNContribution

theorem schurContribution_eq
    (B : BoundarySourceSurface source L) :
    source.coupling = source.multiSchur :=
  B.contributions.schurContribution

theorem matrixDerivedFromSource
    (B : BoundarySourceSurface source L) :
    MatrixDerivedFrom source L B.interface.provenance.carrier
      B.interface.provenance.matrixPackage.matrix :=
  B.contributions.matrixDerivedFromSource

theorem noCutSpecCarrierClaim_at
    (B : BoundarySourceSurface source L) (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  B.noFreeBoundaryData.noCutSpecCarrierClaim k

theorem fromRecursiveRoute_status
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).interface.provenance.signatureDecision.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem fromRecursiveRoute_route
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).interface.route = BoundarySourceRoute.recursiveHistory := by
  rfl

theorem fromRecursiveRoute_consumptionPolicy
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).consumptionPolicy =
      BoundarySourceConsumptionPolicy.boundarySourceOnly := by
  rfl

end BoundarySourceSurface

structure BoundarySourceConvergenceLedger
    (source : ArithmeticSource Cell T) (L : Nat) where
  surface : BoundarySourceSurface source L
  status : BoundarySourceConvergenceStatus
  status_recursiveWitness :
    status = BoundarySourceConvergenceStatus.recursiveWitness
  generatedRouteStatus : GeneratedSubstrateRouteStatus
  generatedRouteStatus_conditionalOpen :
    generatedRouteStatus = GeneratedSubstrateRouteStatus.conditionalOpen
  recursiveRoute : BoundarySourceRoute
  recursiveRoute_eq_recursiveHistory :
    recursiveRoute = BoundarySourceRoute.recursiveHistory
  consumptionPolicy : BoundarySourceConsumptionPolicy
  consumptionPolicy_interfaceOnly :
    consumptionPolicy = BoundarySourceConsumptionPolicy.boundarySourceOnly
  noFreeBoundaryData : BoundarySourceNoFreeBoundaryData surface.interface

namespace BoundarySourceConvergenceLedger

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromRecursiveRoute (R : RecursiveLevelHistoryRoute source L) :
    BoundarySourceConvergenceLedger source L where
  surface := BoundarySourceSurface.fromRecursiveRoute R
  status := BoundarySourceConvergenceStatus.recursiveWitness
  status_recursiveWitness := by
    rfl
  generatedRouteStatus := GeneratedSubstrateRouteStatus.conditionalOpen
  generatedRouteStatus_conditionalOpen := by
    rfl
  recursiveRoute := BoundarySourceRoute.recursiveHistory
  recursiveRoute_eq_recursiveHistory := by
    rfl
  consumptionPolicy := BoundarySourceConsumptionPolicy.boundarySourceOnly
  consumptionPolicy_interfaceOnly := by
    rfl
  noFreeBoundaryData := (BoundarySourceSurface.fromRecursiveRoute R).noFreeBoundaryData

theorem fromRecursiveRoute_status
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).status =
      BoundarySourceConvergenceStatus.recursiveWitness := by
  rfl

theorem fromRecursiveRoute_generated_conditional
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).generatedRouteStatus =
      GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem fromRecursiveRoute_consumptionPolicy
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).consumptionPolicy =
      BoundarySourceConsumptionPolicy.boundarySourceOnly := by
  rfl

theorem fromRecursiveRoute_surface_route
    (R : RecursiveLevelHistoryRoute source L) :
    (fromRecursiveRoute R).surface.interface.route =
      BoundarySourceRoute.recursiveHistory := by
  rfl

end BoundarySourceConvergenceLedger

end BoundarySource

namespace StrengtheningAR2b3

abbrev AR2b3BoundarySourceConvergenceStatus :=
  BoundarySource.BoundarySourceConvergenceStatus

abbrev AR2b3BoundarySourceConsumptionPolicy :=
  BoundarySource.BoundarySourceConsumptionPolicy

abbrev AR2b3BoundarySourceOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.BoundarySourceSurface (Cell := Cell) (T := T) source L

abbrev AR2b3BoundarySourceConvergenceLedgerOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.BoundarySourceConvergenceLedger (Cell := Cell) (T := T) source L

def ar2b3BoundarySourceFromRecursiveRoute
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    AR2b3BoundarySourceOf source L :=
  BoundarySource.BoundarySourceSurface.fromRecursiveRoute R

def ar2b3BoundarySourceConvergenceLedgerFromRecursiveRoute
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    AR2b3BoundarySourceConvergenceLedgerOf source L :=
  BoundarySource.BoundarySourceConvergenceLedger.fromRecursiveRoute R

theorem ar2b3BoundarySourceFromRecursiveRoute_route
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    (ar2b3BoundarySourceFromRecursiveRoute R).interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory := by
  rfl

theorem ar2b3BoundarySourceConvergenceLedger_status
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    (ar2b3BoundarySourceConvergenceLedgerFromRecursiveRoute R).status =
      BoundarySource.BoundarySourceConvergenceStatus.recursiveWitness := by
  rfl

theorem ar2b3BoundarySourceConvergenceLedger_generated_conditional
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (R : BoundarySource.RecursiveLevelHistoryRoute source L) :
    (ar2b3BoundarySourceConvergenceLedgerFromRecursiveRoute R).generatedRouteStatus =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

end StrengtheningAR2b3

end CNNA.PillarA.Arithmetic
