import CNNA.PillarA.Arithmetic.Actions.ActionPackage

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Actions

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

inductive GeneratorActionCandidateKind where
  | branchingTreePartial
  | brightDarkInvolution
  | levelHistoryIdentity
  | mobiusSchurTransfer
  | cmActionCandidate
  | cdActionCandidate
  deriving DecidableEq, Repr

inductive GeneratorActionCandidateStatus where
  | certifiedTrivialBoundaryAction
  | blockedUntilActionMapLawPreservation
  | blockedUntilLaterInternalCarrier
  deriving DecidableEq, Repr

inductive ActionMapDiscipline where
  | certified
  | notYetConstructed
  deriving DecidableEq, Repr

inductive ActionLawDiscipline where
  | certified
  | notYetConstructed
  deriving DecidableEq, Repr

inductive ActionPreservationDiscipline where
  | certified
  | notYetConstructed
  deriving DecidableEq, Repr

inductive ActionFormatDecisionGateStatus where
  | requiredForAR3b
  deriving DecidableEq, Repr

structure GeneratorActionCandidate
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) where
  kind : GeneratorActionCandidateKind
  status : GeneratorActionCandidateStatus
  carrierDiscipline : ActionCarrierDiscipline
  actionMapDiscipline : ActionMapDiscipline
  lawDiscipline : ActionLawDiscipline
  preservationDiscipline : ActionPreservationDiscipline
  actionFormatDecision : ActionFormatDecisionGateStatus
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

namespace GeneratorActionCandidate

variable {source : ArithmeticSource Cell T} {L : Nat}
variable {B : BoundarySource.BoundarySourceSurface source L}

def certifiedLevelHistoryIdentity
    (B : BoundarySource.BoundarySourceSurface source L) :
    GeneratorActionCandidate B where
  kind := GeneratorActionCandidateKind.levelHistoryIdentity
  status := GeneratorActionCandidateStatus.certifiedTrivialBoundaryAction
  carrierDiscipline := ActionCarrierDiscipline.boundarySourceCarrierAnchored
  actionMapDiscipline := ActionMapDiscipline.certified
  lawDiscipline := ActionLawDiscipline.certified
  preservationDiscipline := ActionPreservationDiscipline.certified
  actionFormatDecision := ActionFormatDecisionGateStatus.requiredForAR3b
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

def blockedBoundaryCandidate
    (B : BoundarySource.BoundarySourceSurface source L)
    (kind : GeneratorActionCandidateKind) :
    GeneratorActionCandidate B where
  kind := kind
  status := GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  carrierDiscipline := ActionCarrierDiscipline.boundarySourceCarrierAnchored
  actionMapDiscipline := ActionMapDiscipline.notYetConstructed
  lawDiscipline := ActionLawDiscipline.notYetConstructed
  preservationDiscipline := ActionPreservationDiscipline.notYetConstructed
  actionFormatDecision := ActionFormatDecisionGateStatus.requiredForAR3b
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

def laterInternalCarrierCandidate
    (B : BoundarySource.BoundarySourceSurface source L)
    (kind : GeneratorActionCandidateKind) :
    GeneratorActionCandidate B where
  kind := kind
  status := GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier
  carrierDiscipline := ActionCarrierDiscipline.laterInternalCarrierRequired
  actionMapDiscipline := ActionMapDiscipline.notYetConstructed
  lawDiscipline := ActionLawDiscipline.notYetConstructed
  preservationDiscipline := ActionPreservationDiscipline.notYetConstructed
  actionFormatDecision := ActionFormatDecisionGateStatus.requiredForAR3b
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

theorem route_recursiveHistory
    (C : GeneratorActionCandidate B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  C.routeAnchor

theorem consumptionPolicy_boundarySourceOnly
    (C : GeneratorActionCandidate B) :
    B.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  C.consumptionPolicy

theorem noCutSpecCarrierClaim_at
    (C : GeneratorActionCandidate B) (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  C.noCutSpecCarrierClaim k

theorem fullTreeAutomorphism_blocked
    (C : GeneratorActionCandidate B) :
    C.fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  C.fullTreeAutomorphismStatus_eq

theorem freeLevelPermutation_blocked
    (C : GeneratorActionCandidate B) :
    C.freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  C.freeLevelPermutationStatus_eq

end GeneratorActionCandidate

structure GeneratorActionInventory
    (source : ArithmeticSource Cell T) (L : Nat) where
  boundarySource : BoundarySource.BoundarySourceSurface source L
  levelHistoryIdentityPackage : ActionPackage boundarySource
  levelHistoryIdentityCandidate : GeneratorActionCandidate boundarySource
  levelHistoryIdentityCandidate_status :
    levelHistoryIdentityCandidate.status =
      GeneratorActionCandidateStatus.certifiedTrivialBoundaryAction
  branchingTreePartialCandidate : GeneratorActionCandidate boundarySource
  branchingTreePartialCandidate_status :
    branchingTreePartialCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  brightDarkInvolutionCandidate : GeneratorActionCandidate boundarySource
  brightDarkInvolutionCandidate_status :
    brightDarkInvolutionCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  mobiusSchurTransferCandidate : GeneratorActionCandidate boundarySource
  mobiusSchurTransferCandidate_status :
    mobiusSchurTransferCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation
  cmActionCandidate : GeneratorActionCandidate boundarySource
  cmActionCandidate_status :
    cmActionCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier
  cdActionCandidate : GeneratorActionCandidate boundarySource
  cdActionCandidate_status :
    cdActionCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier
  route : boundarySource.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    boundarySource.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly
  fullTreeAutomorphismStatus : FullTreeAutomorphismStatus
  fullTreeAutomorphismStatus_eq :
    fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  freeLevelPermutationStatus : FreeLevelPermutationStatus
  freeLevelPermutationStatus_eq :
    freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder

namespace GeneratorActionInventory

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromBoundarySource (B : BoundarySource.BoundarySourceSurface source L) :
    GeneratorActionInventory source L where
  boundarySource := B
  levelHistoryIdentityPackage := ActionPackage.identityBoundarySourceAction B
  levelHistoryIdentityCandidate := GeneratorActionCandidate.certifiedLevelHistoryIdentity B
  levelHistoryIdentityCandidate_status := by
    rfl
  branchingTreePartialCandidate :=
    GeneratorActionCandidate.blockedBoundaryCandidate B
      GeneratorActionCandidateKind.branchingTreePartial
  branchingTreePartialCandidate_status := by
    rfl
  brightDarkInvolutionCandidate :=
    GeneratorActionCandidate.blockedBoundaryCandidate B
      GeneratorActionCandidateKind.brightDarkInvolution
  brightDarkInvolutionCandidate_status := by
    rfl
  mobiusSchurTransferCandidate :=
    GeneratorActionCandidate.blockedBoundaryCandidate B
      GeneratorActionCandidateKind.mobiusSchurTransfer
  mobiusSchurTransferCandidate_status := by
    rfl
  cmActionCandidate :=
    GeneratorActionCandidate.laterInternalCarrierCandidate B
      GeneratorActionCandidateKind.cmActionCandidate
  cmActionCandidate_status := by
    rfl
  cdActionCandidate :=
    GeneratorActionCandidate.laterInternalCarrierCandidate B
      GeneratorActionCandidateKind.cdActionCandidate
  cdActionCandidate_status := by
    rfl
  route := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl

theorem route_recursiveHistory
    (I : GeneratorActionInventory source L) :
    I.boundarySource.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  I.route

theorem consumptionPolicy_boundarySourceOnly
    (I : GeneratorActionInventory source L) :
    I.boundarySource.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  I.consumptionPolicy

theorem fullTreeAutomorphism_blocked
    (I : GeneratorActionInventory source L) :
    I.fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  I.fullTreeAutomorphismStatus_eq

theorem freeLevelPermutation_blocked
    (I : GeneratorActionInventory source L) :
    I.freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  I.freeLevelPermutationStatus_eq

theorem levelHistoryIdentity_status
    (I : GeneratorActionInventory source L) :
    I.levelHistoryIdentityCandidate.status =
      GeneratorActionCandidateStatus.certifiedTrivialBoundaryAction :=
  I.levelHistoryIdentityCandidate_status

theorem branchingTreePartial_status
    (I : GeneratorActionInventory source L) :
    I.branchingTreePartialCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation :=
  I.branchingTreePartialCandidate_status

theorem brightDarkInvolution_status
    (I : GeneratorActionInventory source L) :
    I.brightDarkInvolutionCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation :=
  I.brightDarkInvolutionCandidate_status

theorem mobiusSchurTransfer_status
    (I : GeneratorActionInventory source L) :
    I.mobiusSchurTransferCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilActionMapLawPreservation :=
  I.mobiusSchurTransferCandidate_status

theorem cmActionCandidate_has_later_internal_carrier_status
    (I : GeneratorActionInventory source L) :
    I.cmActionCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier :=
  I.cmActionCandidate_status

theorem cdActionCandidate_has_later_internal_carrier_status
    (I : GeneratorActionInventory source L) :
    I.cdActionCandidate.status =
      GeneratorActionCandidateStatus.blockedUntilLaterInternalCarrier :=
  I.cdActionCandidate_status

end GeneratorActionInventory

end Actions

namespace StrengtheningAR3a

abbrev GeneratorActionCandidateKind := Actions.GeneratorActionCandidateKind
abbrev GeneratorActionCandidateStatus := Actions.GeneratorActionCandidateStatus
abbrev ActionMapDiscipline := Actions.ActionMapDiscipline
abbrev ActionLawDiscipline := Actions.ActionLawDiscipline
abbrev ActionPreservationDiscipline := Actions.ActionPreservationDiscipline
abbrev ActionFormatDecisionGateStatus := Actions.ActionFormatDecisionGateStatus

abbrev GeneratorActionCandidateOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :=
  Actions.GeneratorActionCandidate B

abbrev GeneratorActionInventoryOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  Actions.GeneratorActionInventory source L

def generatorActionInventoryFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    GeneratorActionInventoryOf source L :=
  Actions.GeneratorActionInventory.fromBoundarySource B

theorem generatorActionInventory_route
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (generatorActionInventoryFromBoundarySource B).boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Actions.GeneratorActionInventory.route_recursiveHistory
    (generatorActionInventoryFromBoundarySource B)

theorem generatorActionInventory_freeLevelPermutationBlocked
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (generatorActionInventoryFromBoundarySource B).freeLevelPermutationStatus =
      Actions.FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  Actions.GeneratorActionInventory.freeLevelPermutation_blocked
    (generatorActionInventoryFromBoundarySource B)

theorem generatorActionInventory_fullTreeAutomorphismBlocked
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (generatorActionInventoryFromBoundarySource B).fullTreeAutomorphismStatus =
      Actions.FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  Actions.GeneratorActionInventory.fullTreeAutomorphism_blocked
    (generatorActionInventoryFromBoundarySource B)

end StrengtheningAR3a

end CNNA.PillarA.Arithmetic
