import CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

namespace BoundarySource

structure RecursiveLevelHistoryTypeDecision where
  signature : RecursiveHistorySignatureDecision
  carrier_is_LevelHistoryIndex : signature.carrier = CarrierTypeDecision.levelHistoryIndex
  recursiveCarrier_is_witnessAt :
    signature.recursiveCarrier = RecursiveCarrierDecision.witnessAtOverLevelHistoryIndex
  perLevelSource_is_ArithmeticSource :
    signature.perLevelSource =
      PerLevelSourceDecision.arithmeticSourceMultiSchurGeneralizedDtN
  matrixType_is_ExecLevelHistoryMatrix :
    signature.matrixType = MatrixTypeDecision.execLevelHistoryMatrix
  aggregation_is_sourceWitnessToMatrix :
    signature.aggregation = AggregationDecision.sourceWitnessToProofCarryingMatrix
  multiSchur_is_provenanceAnchor :
    signature.multiSchurBinding = MultiSchurBindingDecision.provenanceAnchorAdapterOnly
  interface_is_BoundarySourceInterface :
    signature.interfaceExport = InterfaceExportDecision.boundarySourceInterfaceOnly
  status_closed : signature.status = RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed
  generatedRoute_conditional :
    signature.generatedSubstrateRouteStatus = GeneratedSubstrateRouteStatus.conditionalOpen

namespace RecursiveLevelHistoryTypeDecision

def closed : RecursiveLevelHistoryTypeDecision where
  signature := RecursiveHistorySignatureDecision.closed
  carrier_is_LevelHistoryIndex := by
    rfl
  recursiveCarrier_is_witnessAt := by
    rfl
  perLevelSource_is_ArithmeticSource := by
    rfl
  matrixType_is_ExecLevelHistoryMatrix := by
    rfl
  aggregation_is_sourceWitnessToMatrix := by
    rfl
  multiSchur_is_provenanceAnchor := by
    rfl
  interface_is_BoundarySourceInterface := by
    rfl
  status_closed := by
    rfl
  generatedRoute_conditional := by
    rfl

theorem closed_status :
    closed.signature.status = RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

theorem closed_generatedRoute_conditional :
    closed.signature.generatedSubstrateRouteStatus =
      GeneratedSubstrateRouteStatus.conditionalOpen := by
  rfl

end RecursiveLevelHistoryTypeDecision

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDRecursiveLevelHistoryTypeDecision :=
  BoundarySource.RecursiveLevelHistoryTypeDecision

def ar2bDRecursiveLevelHistoryTypeDecisionClosed :
    AR2bDRecursiveLevelHistoryTypeDecision :=
  BoundarySource.RecursiveLevelHistoryTypeDecision.closed

theorem ar2bDRecursiveLevelHistoryTypeDecisionClosed_status :
    ar2bDRecursiveLevelHistoryTypeDecisionClosed.signature.status =
      BoundarySource.RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed := by
  rfl

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
