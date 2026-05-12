import CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive SchurRecursionNodeKind where
  | root
  | interior
  | leaf
  deriving DecidableEq, Repr

inductive MobiusTransferSourceKind where
  | boundarySource
  | ar3MatrixTransport
  | ar3bActionFormatDiscipline
  deriving DecidableEq, Repr

inductive MobiusTransferParameterStatus where
  | fromBoundarySourceAndAR3Only
  deriving DecidableEq, Repr

inductive MobiusActionDataStatus where
  | preservationAndFormatOnlyNoNumericData
  deriving DecidableEq, Repr

def boundaryMatrixAt
    (B : BoundarySource.BoundarySourceSurface source L)
    (i j : BoundarySource.LevelHistoryIndex L) : ExecComplex :=
  B.interface.matrix (B.indexEmbedding.symm i) (B.indexEmbedding.symm j)

theorem boundaryMatrixAt_eq_interface
    (B : BoundarySource.BoundarySourceSurface source L)
    (i j : BoundarySource.LevelHistoryIndex L) :
    boundaryMatrixAt B i j =
      B.interface.matrix (B.indexEmbedding.symm i) (B.indexEmbedding.symm j) := by
  rfl

structure MobiusTransferParameters
    (B : BoundarySource.BoundarySourceSurface source L) where
  boundarySource : BoundarySource.BoundarySourceSurface source L
  boundarySource_eq : boundarySource = B
  matrixTransportLedger : BoundarySource.AR3MatrixTransportLedger source L
  matrixTransportLedger_eq :
    matrixTransportLedger = BoundarySource.AR3MatrixTransportLedger.fromBoundarySource B
  actionFormatLedger : Actions.ActionFormatDecisionLedger source L
  actionFormatLedger_eq :
    actionFormatLedger = Actions.ActionFormatDecisionLedger.fromBoundarySource B
  transferSource : MobiusTransferSourceKind
  transferSource_eq : transferSource = MobiusTransferSourceKind.boundarySource
  parameterStatus : MobiusTransferParameterStatus
  parameterStatus_eq :
    parameterStatus = MobiusTransferParameterStatus.fromBoundarySourceAndAR3Only
  actionDataStatus : MobiusActionDataStatus
  actionDataStatus_eq :
    actionDataStatus = MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    B.consumptionPolicy = BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly
  branchingCutoffAnchor :
    source.toc.approximant source.concretePolicy = T
  schurEliminationAnchor : source.coupling = source.multiSchur
  ar3bDataDiscipline :
    actionFormatLedger.dataDiscipline =
      Actions.ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace MobiusTransferParameters

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L) :
    MobiusTransferParameters B where
  boundarySource := B
  boundarySource_eq := by
    rfl
  matrixTransportLedger := BoundarySource.AR3MatrixTransportLedger.fromBoundarySource B
  matrixTransportLedger_eq := by
    rfl
  actionFormatLedger := Actions.ActionFormatDecisionLedger.fromBoundarySource B
  actionFormatLedger_eq := by
    rfl
  transferSource := MobiusTransferSourceKind.boundarySource
  transferSource_eq := by
    rfl
  parameterStatus := MobiusTransferParameterStatus.fromBoundarySourceAndAR3Only
  parameterStatus_eq := by
    rfl
  actionDataStatus := MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData
  actionDataStatus_eq := by
    rfl
  route := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  branchingCutoffAnchor := B.noCutSpecCarrierClaim_at (⟨0, Nat.succ_pos L⟩)
  schurEliminationAnchor := B.schurContribution_eq
  ar3bDataDiscipline := by
    rfl
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem boundarySource_eq_anchor
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.boundarySource = B :=
  P.boundarySource_eq

theorem matrixTransportLedger_from_AR3
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.matrixTransportLedger =
      BoundarySource.AR3MatrixTransportLedger.fromBoundarySource B :=
  P.matrixTransportLedger_eq

theorem actionFormatLedger_from_AR3b
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.actionFormatLedger = Actions.ActionFormatDecisionLedger.fromBoundarySource B :=
  P.actionFormatLedger_eq

theorem transferSource_boundarySource
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.transferSource = MobiusTransferSourceKind.boundarySource :=
  P.transferSource_eq

theorem parameterStatus_fromBoundarySourceAndAR3Only
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.parameterStatus = MobiusTransferParameterStatus.fromBoundarySourceAndAR3Only :=
  P.parameterStatus_eq

theorem actionDataStatus_noNumericData
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.actionDataStatus = MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData :=
  P.actionDataStatus_eq

theorem route_recursiveHistory
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.route

theorem branchingCutoffAnchor_from_source
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    source.toc.approximant source.concretePolicy = T :=
  P.branchingCutoffAnchor

theorem schurEliminationAnchor_from_source
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    source.coupling = source.multiSchur :=
  P.schurEliminationAnchor

theorem ar3bDataDiscipline_noNewNumericOrSpectralData
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) :
    P.actionFormatLedger.dataDiscipline =
      Actions.ActionFormatDataDisciplineStatus.formatOnlyNoNewNumericOrSpectralData :=
  P.ar3bDataDiscipline

theorem noCutSpecCarrierClaim_at
    {B : BoundarySource.BoundarySourceSurface source L}
    (P : MobiusTransferParameters B) (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.noCutSpecCarrierClaim k

end MobiusTransferParameters

end Schur

end CNNA.PillarA.Arithmetic
