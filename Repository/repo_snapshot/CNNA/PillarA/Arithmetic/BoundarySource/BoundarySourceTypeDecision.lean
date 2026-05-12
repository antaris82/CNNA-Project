import CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

inductive BoundarySourceRoute where
  | recursiveHistory
  | generatedSubstrate
  deriving DecidableEq, Repr

inductive GeneratedSubstrateRouteStatus where
  | conditionalOpen
  | available
  | obstruction
  deriving DecidableEq, Repr

inductive CarrierTypeDecision where
  | levelHistoryIndex
  deriving DecidableEq, Repr

inductive RecursiveCarrierDecision where
  | witnessAtOverLevelHistoryIndex
  deriving DecidableEq, Repr

inductive PerLevelSourceDecision where
  | arithmeticSourceMultiSchurGeneralizedDtN
  deriving DecidableEq, Repr

inductive MatrixTypeDecision where
  | execLevelHistoryMatrix
  deriving DecidableEq, Repr

inductive AggregationDecision where
  | sourceWitnessToProofCarryingMatrix
  deriving DecidableEq, Repr

inductive MultiSchurBindingDecision where
  | provenanceAnchorAdapterOnly
  deriving DecidableEq, Repr

inductive InterfaceExportDecision where
  | boundarySourceInterfaceOnly
  deriving DecidableEq, Repr

inductive IdealThreadCutSpecCarrierClaimDecision where
  | rejectedForLevelHistoryRoute
  deriving DecidableEq, Repr

inductive FreeBoundaryCarrierDecision where
  | forbiddenByCarrierDecision
  deriving DecidableEq, Repr

inductive FreeMatrixFieldDecision where
  | forbiddenByProofCarryingAggregation
  deriving DecidableEq, Repr

inductive RecursiveTypeDecisionStatus where
  | recursiveTypeDecisionClosed
  | decisionObstruction
  deriving DecidableEq, Repr

structure RecursiveHistorySignatureDecision where
  carrier : CarrierTypeDecision
  recursiveCarrier : RecursiveCarrierDecision
  perLevelSource : PerLevelSourceDecision
  matrixType : MatrixTypeDecision
  aggregation : AggregationDecision
  multiSchurBinding : MultiSchurBindingDecision
  interfaceExport : InterfaceExportDecision
  status : RecursiveTypeDecisionStatus
  generatedSubstrateRouteStatus : GeneratedSubstrateRouteStatus

namespace RecursiveHistorySignatureDecision

def closed : RecursiveHistorySignatureDecision where
  carrier := CarrierTypeDecision.levelHistoryIndex
  recursiveCarrier := RecursiveCarrierDecision.witnessAtOverLevelHistoryIndex
  perLevelSource := PerLevelSourceDecision.arithmeticSourceMultiSchurGeneralizedDtN
  matrixType := MatrixTypeDecision.execLevelHistoryMatrix
  aggregation := AggregationDecision.sourceWitnessToProofCarryingMatrix
  multiSchurBinding := MultiSchurBindingDecision.provenanceAnchorAdapterOnly
  interfaceExport := InterfaceExportDecision.boundarySourceInterfaceOnly
  status := RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed
  generatedSubstrateRouteStatus := GeneratedSubstrateRouteStatus.conditionalOpen

theorem closed_status :
    closed.status = RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem closed_route_generated_conditional :
    closed.generatedSubstrateRouteStatus = GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

theorem closed_carrier :
    closed.carrier = CarrierTypeDecision.levelHistoryIndex := by
  rfl

theorem closed_matrixType :
    closed.matrixType = MatrixTypeDecision.execLevelHistoryMatrix := by
  rfl

theorem closed_interfaceExport :
    closed.interfaceExport = InterfaceExportDecision.boundarySourceInterfaceOnly := by
  rfl

end RecursiveHistorySignatureDecision

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure BoundarySourceProvenance
    (source : ArithmeticSource Cell T) (L : Nat) where
  carrier : RecursiveLevelHistoryCarrier source L
  matrixPackage : LevelHistoryMatrixPackage source L carrier
  adapter : MultiSchurToLevelHistoryAdapter source L carrier
  adapter_package_eq : adapter.package = matrixPackage
  route : BoundarySourceRoute
  route_eq_recursiveHistory : route = BoundarySourceRoute.recursiveHistory
  signatureDecision : RecursiveHistorySignatureDecision
  signatureDecision_closed :
    signatureDecision.status = RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed

namespace BoundarySourceProvenance

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

theorem route_is_recursiveHistory
    (P : BoundarySourceProvenance source L) :
    P.route = BoundarySourceRoute.recursiveHistory :=
  P.route_eq_recursiveHistory

theorem matrixPackage_from_adapter
    (P : BoundarySourceProvenance source L) :
    P.adapter.package = P.matrixPackage :=
  P.adapter_package_eq

theorem decision_is_closed
    (P : BoundarySourceProvenance source L) :
    P.signatureDecision.status = RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed :=
  P.signatureDecision_closed

end BoundarySourceProvenance

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDBoundarySourceRoute := BoundarySource.BoundarySourceRoute
abbrev AR2bDGeneratedSubstrateRouteStatus := BoundarySource.GeneratedSubstrateRouteStatus
abbrev AR2bDRecursiveHistorySignatureDecision := BoundarySource.RecursiveHistorySignatureDecision
abbrev AR2bDBoundarySourceProvenanceOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.BoundarySourceProvenance (Cell := Cell) (T := T) source L

def ar2bDRecursiveHistorySignatureDecisionClosed :
    AR2bDRecursiveHistorySignatureDecision :=
  BoundarySource.RecursiveHistorySignatureDecision.closed

theorem ar2bDRecursiveHistorySignatureDecisionClosed_status :
    ar2bDRecursiveHistorySignatureDecisionClosed.status =
      BoundarySource.RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
