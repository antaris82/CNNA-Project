import CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

namespace BoundarySource

structure BoundarySourceDecisionLedger where
  recursiveTypeDecision : RecursiveLevelHistoryTypeDecision
  recursiveTypeDecisionClosed :
    recursiveTypeDecision.signature.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed
  generatedSubstrateRoute : GeneratedSubstrateRouteLedger
  generatedSubstrateRouteConditional :
    generatedSubstrateRoute.status = GeneratedSubstrateRouteStatus.conditionalOpen
  ar2b2Route : BoundarySourceRoute
  ar2b2Route_eq_recursiveHistory : ar2b2Route = BoundarySourceRoute.recursiveHistory
  idealThreadCutSpecCarrierClaim : IdealThreadCutSpecCarrierClaimDecision
  idealThreadCutSpecCarrierClaim_rejected :
    idealThreadCutSpecCarrierClaim =
      IdealThreadCutSpecCarrierClaimDecision.rejectedForLevelHistoryRoute
  freeBoundaryCarrier : FreeBoundaryCarrierDecision
  freeBoundaryCarrier_forbidden :
    freeBoundaryCarrier = FreeBoundaryCarrierDecision.forbiddenByCarrierDecision
  freeMatrixField : FreeMatrixFieldDecision
  freeMatrixField_forbidden :
    freeMatrixField = FreeMatrixFieldDecision.forbiddenByProofCarryingAggregation
  noFreeBoundaryCarrier :
    recursiveTypeDecision.signature.carrier = CarrierTypeDecision.levelHistoryIndex
  noFreeMatrixDecision :
    recursiveTypeDecision.signature.aggregation =
      AggregationDecision.sourceWitnessToProofCarryingMatrix
  exportOnlyThroughInterface :
    recursiveTypeDecision.signature.interfaceExport =
      InterfaceExportDecision.boundarySourceInterfaceOnly

namespace BoundarySourceDecisionLedger

def closed : BoundarySourceDecisionLedger where
  recursiveTypeDecision := RecursiveLevelHistoryTypeDecision.closed
  recursiveTypeDecisionClosed := by
    rfl
  generatedSubstrateRoute := GeneratedSubstrateRouteLedger.conditionalOpen
  generatedSubstrateRouteConditional := by
    rfl
  ar2b2Route := BoundarySourceRoute.recursiveHistory
  ar2b2Route_eq_recursiveHistory := by
    rfl
  idealThreadCutSpecCarrierClaim :=
    IdealThreadCutSpecCarrierClaimDecision.rejectedForLevelHistoryRoute
  idealThreadCutSpecCarrierClaim_rejected := by
    rfl
  freeBoundaryCarrier := FreeBoundaryCarrierDecision.forbiddenByCarrierDecision
  freeBoundaryCarrier_forbidden := by
    rfl
  freeMatrixField := FreeMatrixFieldDecision.forbiddenByProofCarryingAggregation
  freeMatrixField_forbidden := by
    rfl
  noFreeBoundaryCarrier := by
    rfl
  noFreeMatrixDecision := by
    rfl
  exportOnlyThroughInterface := by
    rfl

theorem closed_status :
    closed.recursiveTypeDecision.signature.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem closed_route :
    closed.ar2b2Route = BoundarySourceRoute.recursiveHistory := by
  rfl

theorem closed_generated_conditional :
    closed.generatedSubstrateRoute.status =
      GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem closed_freeMatrixField_forbidden :
    closed.freeMatrixField =
      FreeMatrixFieldDecision.forbiddenByProofCarryingAggregation := by
  rfl

end BoundarySourceDecisionLedger

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDBoundarySourceDecisionLedger :=
  BoundarySource.BoundarySourceDecisionLedger

def ar2bDBoundarySourceDecisionLedgerClosed :
    AR2bDBoundarySourceDecisionLedger :=
  BoundarySource.BoundarySourceDecisionLedger.closed

theorem ar2bDBoundarySourceDecisionLedgerClosed_status :
    ar2bDBoundarySourceDecisionLedgerClosed.recursiveTypeDecision.signature.status =
      BoundarySource.RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem ar2bDBoundarySourceDecisionLedgerClosed_route :
    ar2bDBoundarySourceDecisionLedgerClosed.ar2b2Route =
      BoundarySource.BoundarySourceRoute.recursiveHistory := by
  rfl

theorem ar2bDBoundarySourceDecisionLedgerClosed_freeMatrixField_forbidden :
    ar2bDBoundarySourceDecisionLedgerClosed.freeMatrixField =
      BoundarySource.FreeMatrixFieldDecision.forbiddenByProofCarryingAggregation := by
  rfl

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
