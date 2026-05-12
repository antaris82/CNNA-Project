import CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Actions

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

inductive ActionFormatKind where
  | globalGroup
  | monoid
  | localTreeAction
  | selfSimilarWreathRecursion
  | branchGroup
  | groupoidPartialAction
  | heckeDoubleCosetOperatorAlgebra
  | profiniteGaloisLikeAction
  | coherentConfigurationMatrixAlgebra
  | pAdicBuildingAction
  | categoricalVOAOrbifoldAction
  | watchlistOnly
  deriving DecidableEq, Repr

inductive RootLatticeActionStatus where
  | rootSystemNotDerived
  | rootlessChiralNotDerived
  | externalLeechComparisonOnly
  deriving DecidableEq, Repr

inductive ActionFormatDecisionStatus where
  | closedForCertifiedTrivialMonoid
  | blockedUntilActionMapLawPreservation
  | blockedUntilLaterInternalCarrier
  deriving DecidableEq, Repr

inductive GlobalActionClaimStatus where
  | trivialMonoidOnlyNoGlobalGroupClaim
  | blockedNoGlobalGroupFromLocalOrPartialData
  | blockedUntilLaterDerivedCarrier
  deriving DecidableEq, Repr

inductive HeckeActionClaimStatus where
  | blockedNoDoubleCosetOrCorrespondenceComposition
  deriving DecidableEq, Repr

inductive ProfiniteGaloisActionClaimStatus where
  | blockedNoDerivedProfiniteOrGaloisCarrier
  deriving DecidableEq, Repr

inductive BuildingActionClaimStatus where
  | blockedNoDerivedBuildingCarrier
  deriving DecidableEq, Repr

inductive VOAOrbifoldActionClaimStatus where
  | blockedNoDerivedCategoricalVOACarrier
  deriving DecidableEq, Repr

inductive ActionFormatCoverageStatus where
  | allAR3aInventoryCandidatesClassified
  deriving DecidableEq, Repr

inductive ActionFormatLedgerStatus where
  | ar3bActionFormatDecisionClosed
  deriving DecidableEq, Repr

inductive ActionFormatDataDisciplineStatus where
  | formatOnlyNoNewNumericOrSpectralData
  deriving DecidableEq, Repr

structure CandidateActionFormatDecision
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) where
  candidate : GeneratorActionCandidate B
  candidateKind : GeneratorActionCandidateKind
  candidateKind_eq : candidate.kind = candidateKind
  candidateStatus : GeneratorActionCandidateStatus
  candidateStatus_eq : candidate.status = candidateStatus
  actionFormatGate : candidate.actionFormatDecision =
    ActionFormatDecisionGateStatus.requiredForAR3b
  format : ActionFormatKind
  rootLatticeStatus : RootLatticeActionStatus
  globalActionClaimStatus : GlobalActionClaimStatus
  heckeActionClaimStatus : HeckeActionClaimStatus
  profiniteGaloisActionClaimStatus : ProfiniteGaloisActionClaimStatus
  buildingActionClaimStatus : BuildingActionClaimStatus
  voaOrbifoldActionClaimStatus : VOAOrbifoldActionClaimStatus
  decisionStatus : ActionFormatDecisionStatus
  routeAnchor : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    B.consumptionPolicy = BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T
  fullTreeAutomorphismStatus : FullTreeAutomorphismStatus
  fullTreeAutomorphismStatus_eq :
    fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  freeLevelPermutationStatus : FreeLevelPermutationStatus
  freeLevelPermutationStatus_eq :
    freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  dataDiscipline : ActionFormatDataDisciplineStatus
  dataDiscipline_eq :
    dataDiscipline = ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData

namespace CandidateActionFormatDecision

variable {source : ArithmeticSource Cell T} {L : Nat}
variable {B : BoundarySource.BoundarySourceSurface source L}

def levelHistoryIdentity
    (B : BoundarySource.BoundarySourceSurface source L) :
    CandidateActionFormatDecision B where
  candidate := GeneratorActionCandidate.certifiedLevelHistoryIdentity B
  candidateKind := GeneratorActionCandidateKind.levelHistoryIdentity
  candidateKind_eq := by
    rfl
  candidateStatus := GeneratorActionCandidateStatus.certifiedTrivialBoundaryAction
  candidateStatus_eq := by
    rfl
  actionFormatGate := by
    rfl
  format := ActionFormatKind.monoid
  rootLatticeStatus := RootLatticeActionStatus.rootSystemNotDerived
  globalActionClaimStatus := GlobalActionClaimStatus.trivialMonoidOnlyNoGlobalGroupClaim
  heckeActionClaimStatus :=
    HeckeActionClaimStatus.blockedNoDoubleCosetOrCorrespondenceComposition
  profiniteGaloisActionClaimStatus :=
    ProfiniteGaloisActionClaimStatus.blockedNoDerivedProfiniteOrGaloisCarrier
  buildingActionClaimStatus := BuildingActionClaimStatus.blockedNoDerivedBuildingCarrier
  voaOrbifoldActionClaimStatus :=
    VOAOrbifoldActionClaimStatus.blockedNoDerivedCategoricalVOACarrier
  decisionStatus := ActionFormatDecisionStatus.closedForCertifiedTrivialMonoid
  routeAnchor := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl

def branchingTreePartial
    (B : BoundarySource.BoundarySourceSurface source L) :
    CandidateActionFormatDecision B where
  candidate := GeneratorActionCandidate.blockedBoundaryCandidate B
    GeneratorActionCandidateKind.branchingTreePartial
  candidateKind := GeneratorActionCandidateKind.branchingTreePartial
  candidateKind_eq := by
    rfl
  candidateStatus := GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  candidateStatus_eq := by
    rfl
  actionFormatGate := by
    rfl
  format := ActionFormatKind.localTreeAction
  rootLatticeStatus := RootLatticeActionStatus.rootSystemNotDerived
  globalActionClaimStatus := GlobalActionClaimStatus.blockedNoGlobalGroupFromLocalOrPartialData
  heckeActionClaimStatus :=
    HeckeActionClaimStatus.blockedNoDoubleCosetOrCorrespondenceComposition
  profiniteGaloisActionClaimStatus :=
    ProfiniteGaloisActionClaimStatus.blockedNoDerivedProfiniteOrGaloisCarrier
  buildingActionClaimStatus := BuildingActionClaimStatus.blockedNoDerivedBuildingCarrier
  voaOrbifoldActionClaimStatus :=
    VOAOrbifoldActionClaimStatus.blockedNoDerivedCategoricalVOACarrier
  decisionStatus := ActionFormatDecisionStatus.blockedUntilActionMapLawPreservation
  routeAnchor := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl

def brightDarkInvolution
    (B : BoundarySource.BoundarySourceSurface source L) :
    CandidateActionFormatDecision B where
  candidate := GeneratorActionCandidate.blockedBoundaryCandidate B
    GeneratorActionCandidateKind.brightDarkInvolution
  candidateKind := GeneratorActionCandidateKind.brightDarkInvolution
  candidateKind_eq := by
    rfl
  candidateStatus := GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  candidateStatus_eq := by
    rfl
  actionFormatGate := by
    rfl
  format := ActionFormatKind.groupoidPartialAction
  rootLatticeStatus := RootLatticeActionStatus.rootSystemNotDerived
  globalActionClaimStatus := GlobalActionClaimStatus.blockedNoGlobalGroupFromLocalOrPartialData
  heckeActionClaimStatus :=
    HeckeActionClaimStatus.blockedNoDoubleCosetOrCorrespondenceComposition
  profiniteGaloisActionClaimStatus :=
    ProfiniteGaloisActionClaimStatus.blockedNoDerivedProfiniteOrGaloisCarrier
  buildingActionClaimStatus := BuildingActionClaimStatus.blockedNoDerivedBuildingCarrier
  voaOrbifoldActionClaimStatus :=
    VOAOrbifoldActionClaimStatus.blockedNoDerivedCategoricalVOACarrier
  decisionStatus := ActionFormatDecisionStatus.blockedUntilActionMapLawPreservation
  routeAnchor := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl

def mobiusSchurTransfer
    (B : BoundarySource.BoundarySourceSurface source L) :
    CandidateActionFormatDecision B where
  candidate := GeneratorActionCandidate.blockedBoundaryCandidate B
    GeneratorActionCandidateKind.mobiusSchurTransfer
  candidateKind := GeneratorActionCandidateKind.mobiusSchurTransfer
  candidateKind_eq := by
    rfl
  candidateStatus := GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  candidateStatus_eq := by
    rfl
  actionFormatGate := by
    rfl
  format := ActionFormatKind.watchlistOnly
  rootLatticeStatus := RootLatticeActionStatus.rootSystemNotDerived
  globalActionClaimStatus := GlobalActionClaimStatus.blockedNoGlobalGroupFromLocalOrPartialData
  heckeActionClaimStatus :=
    HeckeActionClaimStatus.blockedNoDoubleCosetOrCorrespondenceComposition
  profiniteGaloisActionClaimStatus :=
    ProfiniteGaloisActionClaimStatus.blockedNoDerivedProfiniteOrGaloisCarrier
  buildingActionClaimStatus := BuildingActionClaimStatus.blockedNoDerivedBuildingCarrier
  voaOrbifoldActionClaimStatus :=
    VOAOrbifoldActionClaimStatus.blockedNoDerivedCategoricalVOACarrier
  decisionStatus := ActionFormatDecisionStatus.blockedUntilActionMapLawPreservation
  routeAnchor := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl

def cmActionCandidate
    (B : BoundarySource.BoundarySourceSurface source L) :
    CandidateActionFormatDecision B where
  candidate := GeneratorActionCandidate.laterInternalCarrierCandidate B
    GeneratorActionCandidateKind.cmActionCandidate
  candidateKind := GeneratorActionCandidateKind.cmActionCandidate
  candidateKind_eq := by
    rfl
  candidateStatus := GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier
  candidateStatus_eq := by
    rfl
  actionFormatGate := by
    rfl
  format := ActionFormatKind.watchlistOnly
  rootLatticeStatus := RootLatticeActionStatus.rootSystemNotDerived
  globalActionClaimStatus := GlobalActionClaimStatus.blockedUntilLaterDerivedCarrier
  heckeActionClaimStatus :=
    HeckeActionClaimStatus.blockedNoDoubleCosetOrCorrespondenceComposition
  profiniteGaloisActionClaimStatus :=
    ProfiniteGaloisActionClaimStatus.blockedNoDerivedProfiniteOrGaloisCarrier
  buildingActionClaimStatus := BuildingActionClaimStatus.blockedNoDerivedBuildingCarrier
  voaOrbifoldActionClaimStatus :=
    VOAOrbifoldActionClaimStatus.blockedNoDerivedCategoricalVOACarrier
  decisionStatus := ActionFormatDecisionStatus.blockedUntilLaterInternalCarrier
  routeAnchor := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl

def cdActionCandidate
    (B : BoundarySource.BoundarySourceSurface source L) :
    CandidateActionFormatDecision B where
  candidate := GeneratorActionCandidate.laterInternalCarrierCandidate B
    GeneratorActionCandidateKind.cdActionCandidate
  candidateKind := GeneratorActionCandidateKind.cdActionCandidate
  candidateKind_eq := by
    rfl
  candidateStatus := GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier
  candidateStatus_eq := by
    rfl
  actionFormatGate := by
    rfl
  format := ActionFormatKind.watchlistOnly
  rootLatticeStatus := RootLatticeActionStatus.rootSystemNotDerived
  globalActionClaimStatus := GlobalActionClaimStatus.blockedUntilLaterDerivedCarrier
  heckeActionClaimStatus :=
    HeckeActionClaimStatus.blockedNoDoubleCosetOrCorrespondenceComposition
  profiniteGaloisActionClaimStatus :=
    ProfiniteGaloisActionClaimStatus.blockedNoDerivedProfiniteOrGaloisCarrier
  buildingActionClaimStatus := BuildingActionClaimStatus.blockedNoDerivedBuildingCarrier
  voaOrbifoldActionClaimStatus :=
    VOAOrbifoldActionClaimStatus.blockedNoDerivedCategoricalVOACarrier
  decisionStatus := ActionFormatDecisionStatus.blockedUntilLaterInternalCarrier
  routeAnchor := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl

theorem decision_candidate_kind
    (D : CandidateActionFormatDecision B) :
    D.candidate.kind = D.candidateKind :=
  D.candidateKind_eq

theorem decision_candidate_status
    (D : CandidateActionFormatDecision B) :
    D.candidate.status = D.candidateStatus :=
  D.candidateStatus_eq

theorem decision_requires_ar3b_gate
    (D : CandidateActionFormatDecision B) :
    D.candidate.actionFormatDecision = ActionFormatDecisionGateStatus.requiredForAR3b :=
  D.actionFormatGate

theorem decision_route_recursiveHistory
    (D : CandidateActionFormatDecision B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  D.routeAnchor

theorem decision_consumptionPolicy_boundarySourceOnly
    (D : CandidateActionFormatDecision B) :
    B.consumptionPolicy = BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  D.consumptionPolicy

theorem decision_noCutSpecCarrierClaim_at
    (D : CandidateActionFormatDecision B) (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  D.noCutSpecCarrierClaim k

theorem decision_fullTreeAutomorphism_blocked
    (D : CandidateActionFormatDecision B) :
    D.fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  D.fullTreeAutomorphismStatus_eq

theorem decision_freeLevelPermutation_blocked
    (D : CandidateActionFormatDecision B) :
    D.freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  D.freeLevelPermutationStatus_eq

theorem decision_dataDiscipline_formatOnly
    (D : CandidateActionFormatDecision B) :
    D.dataDiscipline = ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData :=
  D.dataDiscipline_eq

end CandidateActionFormatDecision

structure ActionFormatDecisionLedger
    (source : ArithmeticSource Cell T) (L : Nat) where
  inventory : GeneratorActionInventory source L
  levelHistoryIdentityDecision : CandidateActionFormatDecision inventory.boundarySource
  levelHistoryIdentity_covers_inventory :
    levelHistoryIdentityDecision.candidate = inventory.levelHistoryIdentityCandidate
  levelHistoryIdentity_format :
    levelHistoryIdentityDecision.format = ActionFormatKind.monoid
  branchingTreePartialDecision : CandidateActionFormatDecision inventory.boundarySource
  branchingTreePartial_covers_inventory :
    branchingTreePartialDecision.candidate = inventory.branchingTreePartialCandidate
  branchingTreePartial_format :
    branchingTreePartialDecision.format = ActionFormatKind.localTreeAction
  brightDarkInvolutionDecision : CandidateActionFormatDecision inventory.boundarySource
  brightDarkInvolution_covers_inventory :
    brightDarkInvolutionDecision.candidate = inventory.brightDarkInvolutionCandidate
  brightDarkInvolution_format :
    brightDarkInvolutionDecision.format = ActionFormatKind.groupoidPartialAction
  mobiusSchurTransferDecision : CandidateActionFormatDecision inventory.boundarySource
  mobiusSchurTransfer_covers_inventory :
    mobiusSchurTransferDecision.candidate = inventory.mobiusSchurTransferCandidate
  mobiusSchurTransfer_format :
    mobiusSchurTransferDecision.format = ActionFormatKind.watchlistOnly
  cmActionDecision : CandidateActionFormatDecision inventory.boundarySource
  cmAction_covers_inventory :
    cmActionDecision.candidate = inventory.cmActionCandidate
  cmAction_format :
    cmActionDecision.format = ActionFormatKind.watchlistOnly
  cdActionDecision : CandidateActionFormatDecision inventory.boundarySource
  cdAction_covers_inventory :
    cdActionDecision.candidate = inventory.cdActionCandidate
  cdAction_format :
    cdActionDecision.format = ActionFormatKind.watchlistOnly
  coverage : ActionFormatCoverageStatus
  coverage_eq :
    coverage = ActionFormatCoverageStatus.allAR3aInventoryCandidatesClassified
  status : ActionFormatLedgerStatus
  status_eq : status = ActionFormatLedgerStatus.ar3bActionFormatDecisionClosed
  dataDiscipline : ActionFormatDataDisciplineStatus
  dataDiscipline_eq :
    dataDiscipline = ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  route :
    inventory.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    inventory.boundarySource.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly
  fullTreeAutomorphismStatus : FullTreeAutomorphismStatus
  fullTreeAutomorphismStatus_eq :
    fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  freeLevelPermutationStatus : FreeLevelPermutationStatus
  freeLevelPermutationStatus_eq :
    freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder

namespace ActionFormatDecisionLedger

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromBoundarySource (B : BoundarySource.BoundarySourceSurface source L) :
    ActionFormatDecisionLedger source L where
  inventory := GeneratorActionInventory.fromBoundarySource B
  levelHistoryIdentityDecision := CandidateActionFormatDecision.levelHistoryIdentity B
  levelHistoryIdentity_covers_inventory := by
    rfl
  levelHistoryIdentity_format := by
    rfl
  branchingTreePartialDecision := CandidateActionFormatDecision.branchingTreePartial B
  branchingTreePartial_covers_inventory := by
    rfl
  branchingTreePartial_format := by
    rfl
  brightDarkInvolutionDecision := CandidateActionFormatDecision.brightDarkInvolution B
  brightDarkInvolution_covers_inventory := by
    rfl
  brightDarkInvolution_format := by
    rfl
  mobiusSchurTransferDecision := CandidateActionFormatDecision.mobiusSchurTransfer B
  mobiusSchurTransfer_covers_inventory := by
    rfl
  mobiusSchurTransfer_format := by
    rfl
  cmActionDecision := CandidateActionFormatDecision.cmActionCandidate B
  cmAction_covers_inventory := by
    rfl
  cmAction_format := by
    rfl
  cdActionDecision := CandidateActionFormatDecision.cdActionCandidate B
  cdAction_covers_inventory := by
    rfl
  cdAction_format := by
    rfl
  coverage := ActionFormatCoverageStatus.allAR3aInventoryCandidatesClassified
  coverage_eq := by
    rfl
  status := ActionFormatLedgerStatus.ar3bActionFormatDecisionClosed
  status_eq := by
    rfl
  dataDiscipline := ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  dataDiscipline_eq := by
    rfl
  route := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl

theorem ledger_coverage_allCandidatesClassified
    (D : ActionFormatDecisionLedger source L) :
    D.coverage = ActionFormatCoverageStatus.allAR3aInventoryCandidatesClassified :=
  D.coverage_eq

theorem ledger_status_closed
    (D : ActionFormatDecisionLedger source L) :
    D.status = ActionFormatLedgerStatus.ar3bActionFormatDecisionClosed :=
  D.status_eq

theorem ledger_dataDiscipline_formatOnly
    (D : ActionFormatDecisionLedger source L) :
    D.dataDiscipline = ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData :=
  D.dataDiscipline_eq

theorem ledger_route_recursiveHistory
    (D : ActionFormatDecisionLedger source L) :
    D.inventory.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  D.route

theorem ledger_consumptionPolicy_boundarySourceOnly
    (D : ActionFormatDecisionLedger source L) :
    D.inventory.boundarySource.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  D.consumptionPolicy

theorem ledger_fullTreeAutomorphism_blocked
    (D : ActionFormatDecisionLedger source L) :
    D.fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  D.fullTreeAutomorphismStatus_eq

theorem ledger_freeLevelPermutation_blocked
    (D : ActionFormatDecisionLedger source L) :
    D.freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  D.freeLevelPermutationStatus_eq

theorem ledger_levelHistoryIdentity_format_monoid
    (D : ActionFormatDecisionLedger source L) :
    D.levelHistoryIdentityDecision.format = ActionFormatKind.monoid :=
  D.levelHistoryIdentity_format

theorem ledger_branchingTreePartial_format_localTree
    (D : ActionFormatDecisionLedger source L) :
    D.branchingTreePartialDecision.format = ActionFormatKind.localTreeAction :=
  D.branchingTreePartial_format

theorem ledger_brightDarkInvolution_format_groupoidPartial
    (D : ActionFormatDecisionLedger source L) :
    D.brightDarkInvolutionDecision.format = ActionFormatKind.groupoidPartialAction :=
  D.brightDarkInvolution_format

theorem ledger_mobiusSchurTransfer_format_watchlistOnly
    (D : ActionFormatDecisionLedger source L) :
    D.mobiusSchurTransferDecision.format = ActionFormatKind.watchlistOnly :=
  D.mobiusSchurTransfer_format

theorem ledger_cmAction_format_watchlistOnly
    (D : ActionFormatDecisionLedger source L) :
    D.cmActionDecision.format = ActionFormatKind.watchlistOnly :=
  D.cmAction_format

theorem ledger_cdAction_format_watchlistOnly
    (D : ActionFormatDecisionLedger source L) :
    D.cdActionDecision.format = ActionFormatKind.watchlistOnly :=
  D.cdAction_format

end ActionFormatDecisionLedger

end Actions

namespace StrengtheningAR3b

abbrev ActionFormatKind := Actions.ActionFormatKind
abbrev RootLatticeActionStatus := Actions.RootLatticeActionStatus
abbrev ActionFormatDecisionStatus := Actions.ActionFormatDecisionStatus
abbrev GlobalActionClaimStatus := Actions.GlobalActionClaimStatus
abbrev HeckeActionClaimStatus := Actions.HeckeActionClaimStatus
abbrev ProfiniteGaloisActionClaimStatus := Actions.ProfiniteGaloisActionClaimStatus
abbrev BuildingActionClaimStatus := Actions.BuildingActionClaimStatus
abbrev VOAOrbifoldActionClaimStatus := Actions.VOAOrbifoldActionClaimStatus
abbrev ActionFormatCoverageStatus := Actions.ActionFormatCoverageStatus
abbrev ActionFormatLedgerStatus := Actions.ActionFormatLedgerStatus
abbrev ActionFormatDataDisciplineStatus := Actions.ActionFormatDataDisciplineStatus

abbrev CandidateActionFormatDecisionOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :=
  Actions.CandidateActionFormatDecision B

abbrev ActionFormatDecisionLedgerOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  Actions.ActionFormatDecisionLedger source L

def actionFormatDecisionLedgerFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    ActionFormatDecisionLedgerOf source L :=
  Actions.ActionFormatDecisionLedger.fromBoundarySource B

theorem actionFormatDecisionLedger_status_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (actionFormatDecisionLedgerFromBoundarySource B).status =
      Actions.ActionFormatLedgerStatus.ar3bActionFormatDecisionClosed :=
  Actions.ActionFormatDecisionLedger.ledger_status_closed
    (actionFormatDecisionLedgerFromBoundarySource B)

theorem actionFormatDecisionLedger_coverage_allCandidatesClassified
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (actionFormatDecisionLedgerFromBoundarySource B).coverage =
      Actions.ActionFormatCoverageStatus.allAR3aInventoryCandidatesClassified :=
  Actions.ActionFormatDecisionLedger.ledger_coverage_allCandidatesClassified
    (actionFormatDecisionLedgerFromBoundarySource B)

theorem actionFormatDecisionLedger_route_recursiveHistory
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (actionFormatDecisionLedgerFromBoundarySource B).inventory.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Actions.ActionFormatDecisionLedger.ledger_route_recursiveHistory
    (actionFormatDecisionLedgerFromBoundarySource B)

theorem actionFormatDecisionLedger_freeLevelPermutation_blocked
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (actionFormatDecisionLedgerFromBoundarySource B).freeLevelPermutationStatus =
      Actions.FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  Actions.ActionFormatDecisionLedger.ledger_freeLevelPermutation_blocked
    (actionFormatDecisionLedgerFromBoundarySource B)

theorem actionFormatDecisionLedger_fullTreeAutomorphism_blocked
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (actionFormatDecisionLedgerFromBoundarySource B).fullTreeAutomorphismStatus =
      Actions.FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  Actions.ActionFormatDecisionLedger.ledger_fullTreeAutomorphism_blocked
    (actionFormatDecisionLedgerFromBoundarySource B)

end StrengtheningAR3b

end CNNA.PillarA.Arithmetic
