import CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

namespace BoundarySource

namespace HistoryExpandedSubstrate

def ledger : GeneratedSubstrateCandidateLedger :=
  GeneratedSubstrateCandidateLedger.historyExpanded

theorem ledger_kind :
    ledger.kind = GeneratedSubstrateCandidateKind.historyExpanded := by
  rfl

theorem ledger_status :
    ledger.status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem ledger_blocker :
    ledger.blocker =
      GeneratedSubstrateBlocker.missingAInternalNonSingletonSubstrate := by
  rfl

theorem ledger_noFreeCarrier :
    ledger.obligations.carrierPolicy = GeneratedSubstrateCarrierPolicy.noFreeCarrier := by
  rfl

theorem ledger_noFinCarrier :
    ledger.obligations.indexPolicy =
      GeneratedSubstrateIndexPolicy.noFinIndexAsSubstrateCarrier := by
  rfl

theorem ledger_portsDoNotCreateCarrierPoints :
    ledger.obligations.boundaryPortsPolicy =
      GeneratedSubstrateBoundaryPortsPolicy.portsDoNotCreateCarrierPoints := by
  rfl

end HistoryExpandedSubstrate

end BoundarySource

namespace StrengtheningAR2b1

def ar2b1HistoryExpandedSubstrateLedger :
    BoundarySource.GeneratedSubstrateCandidateLedger :=
  BoundarySource.HistoryExpandedSubstrate.ledger

theorem ar2b1HistoryExpandedSubstrate_status :
    ar2b1HistoryExpandedSubstrateLedger.status =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem ar2b1HistoryExpandedSubstrate_noFreeCarrier :
    ar2b1HistoryExpandedSubstrateLedger.obligations.carrierPolicy =
      BoundarySource.GeneratedSubstrateCarrierPolicy.noFreeCarrier := by
  rfl

end StrengtheningAR2b1

end CNNA.PillarA.Arithmetic
