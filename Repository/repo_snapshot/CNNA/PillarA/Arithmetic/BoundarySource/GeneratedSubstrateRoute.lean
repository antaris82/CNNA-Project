import CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

namespace BoundarySource

inductive GeneratedSubstrateCandidateKind where
  | branchAddress
  | boundaryState
  | historyExpanded
  | interfaceExposure
  deriving DecidableEq, Repr

inductive GeneratedSubstrateBlocker where
  | missingAInternalNonSingletonSubstrate
  deriving DecidableEq, Repr

inductive GeneratedSubstrateCarrierPolicy where
  | noFreeCarrier
  deriving DecidableEq, Repr

inductive GeneratedSubstrateIndexPolicy where
  | noFinIndexAsSubstrateCarrier
  deriving DecidableEq, Repr

inductive GeneratedSubstrateBoundaryPortsPolicy where
  | portsDoNotCreateCarrierPoints
  deriving DecidableEq, Repr

inductive GeneratedSubstrateExternalGeometryPolicy where
  | noExternalPCFImport
  deriving DecidableEq, Repr

inductive GeneratedSubstrateProvenancePolicy where
  | requireBranchCutoffSectorCouplingOrSchurDtN
  deriving DecidableEq, Repr

structure GeneratedSubstrateCandidateObligations where
  carrierPolicy : GeneratedSubstrateCarrierPolicy
  carrierPolicy_noFreeCarrier :
    carrierPolicy = GeneratedSubstrateCarrierPolicy.noFreeCarrier
  indexPolicy : GeneratedSubstrateIndexPolicy
  indexPolicy_noFinCarrier :
    indexPolicy = GeneratedSubstrateIndexPolicy.noFinIndexAsSubstrateCarrier
  boundaryPortsPolicy : GeneratedSubstrateBoundaryPortsPolicy
  boundaryPorts_noGeneratedPoints :
    boundaryPortsPolicy =
      GeneratedSubstrateBoundaryPortsPolicy.portsDoNotCreateCarrierPoints
  externalGeometryPolicy : GeneratedSubstrateExternalGeometryPolicy
  externalGeometry_noPCFImport :
    externalGeometryPolicy = GeneratedSubstrateExternalGeometryPolicy.noExternalPCFImport
  provenancePolicy : GeneratedSubstrateProvenancePolicy
  provenance_required :
    provenancePolicy =
      GeneratedSubstrateProvenancePolicy.requireBranchCutoffSectorCouplingOrSchurDtN

namespace GeneratedSubstrateCandidateObligations

def strict : GeneratedSubstrateCandidateObligations where
  carrierPolicy := GeneratedSubstrateCarrierPolicy.noFreeCarrier
  carrierPolicy_noFreeCarrier := by
    rfl
  indexPolicy := GeneratedSubstrateIndexPolicy.noFinIndexAsSubstrateCarrier
  indexPolicy_noFinCarrier := by
    rfl
  boundaryPortsPolicy :=
    GeneratedSubstrateBoundaryPortsPolicy.portsDoNotCreateCarrierPoints
  boundaryPorts_noGeneratedPoints := by
    rfl
  externalGeometryPolicy := GeneratedSubstrateExternalGeometryPolicy.noExternalPCFImport
  externalGeometry_noPCFImport := by
    rfl
  provenancePolicy :=
    GeneratedSubstrateProvenancePolicy.requireBranchCutoffSectorCouplingOrSchurDtN
  provenance_required := by
    rfl

theorem strict_noFreeCarrier :
    strict.carrierPolicy = GeneratedSubstrateCarrierPolicy.noFreeCarrier := by
  rfl

theorem strict_noFinCarrier :
    strict.indexPolicy =
      GeneratedSubstrateIndexPolicy.noFinIndexAsSubstrateCarrier := by
  rfl

theorem strict_portsDoNotCreatePoints :
    strict.boundaryPortsPolicy =
      GeneratedSubstrateBoundaryPortsPolicy.portsDoNotCreateCarrierPoints := by
  rfl

theorem strict_noPCFImport :
    strict.externalGeometryPolicy =
      GeneratedSubstrateExternalGeometryPolicy.noExternalPCFImport := by
  rfl

theorem strict_provenanceRequired :
    strict.provenancePolicy =
      GeneratedSubstrateProvenancePolicy.requireBranchCutoffSectorCouplingOrSchurDtN := by
  rfl

end GeneratedSubstrateCandidateObligations

structure GeneratedSubstrateCandidateLedger where
  kind : GeneratedSubstrateCandidateKind
  status : GeneratedSubstrateRouteStatus
  status_conditionalOpen : status = GeneratedSubstrateRouteStatus.conditionalOpen
  blocker : GeneratedSubstrateBlocker
  blocker_missingCarrier :
    blocker = GeneratedSubstrateBlocker.missingAInternalNonSingletonSubstrate
  obligations : GeneratedSubstrateCandidateObligations
  obligations_strict : obligations = GeneratedSubstrateCandidateObligations.strict
  notPositiveBoundarySource : True
  notImplementationBasisForAR2b2 : True

namespace GeneratedSubstrateCandidateLedger

def conditionalOpen (kind : GeneratedSubstrateCandidateKind) :
    GeneratedSubstrateCandidateLedger where
  kind := kind
  status := GeneratedSubstrateRouteStatus.conditionalOpen
  status_conditionalOpen := by
    rfl
  blocker := GeneratedSubstrateBlocker.missingAInternalNonSingletonSubstrate
  blocker_missingCarrier := by
    rfl
  obligations := GeneratedSubstrateCandidateObligations.strict
  obligations_strict := by
    rfl
  notPositiveBoundarySource := True.intro
  notImplementationBasisForAR2b2 := True.intro

def branchAddress : GeneratedSubstrateCandidateLedger :=
  conditionalOpen GeneratedSubstrateCandidateKind.branchAddress

def boundaryState : GeneratedSubstrateCandidateLedger :=
  conditionalOpen GeneratedSubstrateCandidateKind.boundaryState

def historyExpanded : GeneratedSubstrateCandidateLedger :=
  conditionalOpen GeneratedSubstrateCandidateKind.historyExpanded

def interfaceExposure : GeneratedSubstrateCandidateLedger :=
  conditionalOpen GeneratedSubstrateCandidateKind.interfaceExposure

theorem conditionalOpen_status (kind : GeneratedSubstrateCandidateKind) :
    (conditionalOpen kind).status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem conditionalOpen_blocker (kind : GeneratedSubstrateCandidateKind) :
    (conditionalOpen kind).blocker =
      GeneratedSubstrateBlocker.missingAInternalNonSingletonSubstrate := by
  rfl

theorem conditionalOpen_obligations (kind : GeneratedSubstrateCandidateKind) :
    (conditionalOpen kind).obligations = GeneratedSubstrateCandidateObligations.strict := by
  rfl

theorem branchAddress_kind :
    branchAddress.kind = GeneratedSubstrateCandidateKind.branchAddress := by
  rfl

theorem boundaryState_kind :
    boundaryState.kind = GeneratedSubstrateCandidateKind.boundaryState := by
  rfl

theorem historyExpanded_kind :
    historyExpanded.kind = GeneratedSubstrateCandidateKind.historyExpanded := by
  rfl

theorem interfaceExposure_kind :
    interfaceExposure.kind = GeneratedSubstrateCandidateKind.interfaceExposure := by
  rfl

end GeneratedSubstrateCandidateLedger

structure GeneratedSubstrateRouteLedger where
  status : GeneratedSubstrateRouteStatus
  notImplementationBasisForAR2b2 : status = GeneratedSubstrateRouteStatus.conditionalOpen

namespace GeneratedSubstrateRouteLedger

def conditionalOpen : GeneratedSubstrateRouteLedger where
  status := GeneratedSubstrateRouteStatus.conditionalOpen
  notImplementationBasisForAR2b2 := by
    rfl

theorem conditionalOpen_status :
    conditionalOpen.status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

end GeneratedSubstrateRouteLedger

structure GeneratedSubstrateRouteInventory where
  routeStatus : GeneratedSubstrateRouteStatus
  routeStatus_conditionalOpen : routeStatus = GeneratedSubstrateRouteStatus.conditionalOpen
  branchAddress : GeneratedSubstrateCandidateLedger
  branchAddress_kind : branchAddress.kind = GeneratedSubstrateCandidateKind.branchAddress
  branchAddress_status : branchAddress.status = GeneratedSubstrateRouteStatus.conditionalOpen
  boundaryState : GeneratedSubstrateCandidateLedger
  boundaryState_kind : boundaryState.kind = GeneratedSubstrateCandidateKind.boundaryState
  boundaryState_status : boundaryState.status = GeneratedSubstrateRouteStatus.conditionalOpen
  historyExpanded : GeneratedSubstrateCandidateLedger
  historyExpanded_kind : historyExpanded.kind = GeneratedSubstrateCandidateKind.historyExpanded
  historyExpanded_status : historyExpanded.status = GeneratedSubstrateRouteStatus.conditionalOpen
  interfaceExposure : GeneratedSubstrateCandidateLedger
  interfaceExposure_kind : interfaceExposure.kind = GeneratedSubstrateCandidateKind.interfaceExposure
  interfaceExposure_status : interfaceExposure.status = GeneratedSubstrateRouteStatus.conditionalOpen
  noCandidateIsPositiveSource : True
  recursiveRouteRemainsImplementationBasis : True

namespace GeneratedSubstrateRouteInventory

def conditionalOpen : GeneratedSubstrateRouteInventory where
  routeStatus := GeneratedSubstrateRouteStatus.conditionalOpen
  routeStatus_conditionalOpen := by
    rfl
  branchAddress := GeneratedSubstrateCandidateLedger.branchAddress
  branchAddress_kind := by
    rfl
  branchAddress_status := by
    rfl
  boundaryState := GeneratedSubstrateCandidateLedger.boundaryState
  boundaryState_kind := by
    rfl
  boundaryState_status := by
    rfl
  historyExpanded := GeneratedSubstrateCandidateLedger.historyExpanded
  historyExpanded_kind := by
    rfl
  historyExpanded_status := by
    rfl
  interfaceExposure := GeneratedSubstrateCandidateLedger.interfaceExposure
  interfaceExposure_kind := by
    rfl
  interfaceExposure_status := by
    rfl
  noCandidateIsPositiveSource := True.intro
  recursiveRouteRemainsImplementationBasis := True.intro

theorem conditionalOpen_status :
    conditionalOpen.routeStatus = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem conditionalOpen_branchAddress_status :
    conditionalOpen.branchAddress.status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem conditionalOpen_boundaryState_status :
    conditionalOpen.boundaryState.status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem conditionalOpen_historyExpanded_status :
    conditionalOpen.historyExpanded.status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem conditionalOpen_interfaceExposure_status :
    conditionalOpen.interfaceExposure.status = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

end GeneratedSubstrateRouteInventory

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDGeneratedSubstrateRouteLedger :=
  BoundarySource.GeneratedSubstrateRouteLedger

def ar2bDGeneratedSubstrateRouteConditionalOpen :
    AR2bDGeneratedSubstrateRouteLedger :=
  BoundarySource.GeneratedSubstrateRouteLedger.conditionalOpen

end StrengtheningAR2bD

namespace StrengtheningAR2b1

abbrev AR2b1GeneratedSubstrateCandidateKind :=
  BoundarySource.GeneratedSubstrateCandidateKind

abbrev AR2b1GeneratedSubstrateCandidateLedger :=
  BoundarySource.GeneratedSubstrateCandidateLedger

abbrev AR2b1GeneratedSubstrateRouteInventory :=
  BoundarySource.GeneratedSubstrateRouteInventory

def ar2b1GeneratedSubstrateRouteInventoryConditionalOpen :
    AR2b1GeneratedSubstrateRouteInventory :=
  BoundarySource.GeneratedSubstrateRouteInventory.conditionalOpen

theorem ar2b1GeneratedSubstrateRouteInventory_status :
    ar2b1GeneratedSubstrateRouteInventoryConditionalOpen.routeStatus =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem ar2b1BranchAddress_status :
    ar2b1GeneratedSubstrateRouteInventoryConditionalOpen.branchAddress.status =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem ar2b1BoundaryState_status :
    ar2b1GeneratedSubstrateRouteInventoryConditionalOpen.boundaryState.status =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem ar2b1HistoryExpanded_status :
    ar2b1GeneratedSubstrateRouteInventoryConditionalOpen.historyExpanded.status =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem ar2b1InterfaceExposure_status :
    ar2b1GeneratedSubstrateRouteInventoryConditionalOpen.interfaceExposure.status =
      BoundarySource.GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

end StrengtheningAR2b1

end CNNA.PillarA.Arithmetic
