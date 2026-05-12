import CNNA.PillarA.Arithmetic.Core.MatrixTransport

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

inductive AR3ProfileMatrixKind where
  | brightBrightSchur
  | dtn
  | char
  deriving DecidableEq, Repr

structure AR3BoundaryTransportAnchors
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySourceSurface source L) where
  dtnContribution : source.dtn = source.multiSchur.binary
  generalizedDtNContribution : source.generalizedDtN = source.multiSchur.generalized
  brightBrightSchurContribution : source.coupling = source.multiSchur
  matrixDerivedFromSource :
    MatrixDerivedFrom source L B.interface.provenance.carrier
      B.interface.provenance.matrixPackage.matrix
  noCutSpecCarrierClaim :
    ∀ _k : LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T
  route : B.interface.route = BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    B.consumptionPolicy = BoundarySourceConsumptionPolicy.boundarySourceOnly

namespace AR3BoundaryTransportAnchors

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromBoundarySource (B : BoundarySourceSurface source L) :
    AR3BoundaryTransportAnchors B where
  dtnContribution := B.dtnContribution_eq
  generalizedDtNContribution := B.generalizedDtNContribution_eq
  brightBrightSchurContribution := B.schurContribution_eq
  matrixDerivedFromSource := B.matrixDerivedFromSource
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  route := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly

theorem dtnContribution_eq
    {B : BoundarySourceSurface source L}
    (A : AR3BoundaryTransportAnchors B) :
    source.dtn = source.multiSchur.binary :=
  A.dtnContribution

theorem generalizedDtNContribution_eq
    {B : BoundarySourceSurface source L}
    (A : AR3BoundaryTransportAnchors B) :
    source.generalizedDtN = source.multiSchur.generalized :=
  A.generalizedDtNContribution

theorem brightBrightSchurContribution_eq
    {B : BoundarySourceSurface source L}
    (A : AR3BoundaryTransportAnchors B) :
    source.coupling = source.multiSchur :=
  A.brightBrightSchurContribution

theorem noCutSpecCarrierClaim_at
    {B : BoundarySourceSurface source L}
    (A : AR3BoundaryTransportAnchors B) (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  A.noCutSpecCarrierClaim k

end AR3BoundaryTransportAnchors

structure AR3BoundaryMatrixProfile
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySourceSurface source L) where
  kind : AR3ProfileMatrixKind
  matrix : Matrix B.interface.index B.interface.index ExecComplex
  matrix_eq_boundarySource : matrix = B.interface.matrix
  anchors : AR3BoundaryTransportAnchors B

namespace AR3BoundaryMatrixProfile

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromBoundarySource
    (B : BoundarySourceSurface source L) (kind : AR3ProfileMatrixKind) :
    AR3BoundaryMatrixProfile B where
  kind := kind
  matrix := B.interface.matrix
  matrix_eq_boundarySource := by
    rfl
  anchors := AR3BoundaryTransportAnchors.fromBoundarySource B

def brightBrightSchur (B : BoundarySourceSurface source L) :
    AR3BoundaryMatrixProfile B :=
  fromBoundarySource B AR3ProfileMatrixKind.brightBrightSchur

def dtn (B : BoundarySourceSurface source L) :
    AR3BoundaryMatrixProfile B :=
  fromBoundarySource B AR3ProfileMatrixKind.dtn

def char (B : BoundarySourceSurface source L) :
    AR3BoundaryMatrixProfile B :=
  fromBoundarySource B AR3ProfileMatrixKind.char

theorem matrix_eq_boundarySource_holds
    {B : BoundarySourceSurface source L}
    (P : AR3BoundaryMatrixProfile B) :
    P.matrix = B.interface.matrix :=
  P.matrix_eq_boundarySource

theorem component_identity
    {B : BoundarySourceSurface source L}
    (P : AR3BoundaryMatrixProfile B)
    (i j : B.interface.index) :
    P.matrix i j = B.interface.matrix i j := by
  rw [P.matrix_eq_boundarySource]

theorem route_recursiveHistory
    {B : BoundarySourceSurface source L}
    (P : AR3BoundaryMatrixProfile B) :
    B.interface.route = BoundarySourceRoute.recursiveHistory :=
  P.anchors.route

theorem matrixDerivedFromSource
    {B : BoundarySourceSurface source L}
    (P : AR3BoundaryMatrixProfile B) :
    MatrixDerivedFrom source L B.interface.provenance.carrier
      B.interface.provenance.matrixPackage.matrix :=
  P.anchors.matrixDerivedFromSource

theorem noCutSpecCarrierClaim_at
    {B : BoundarySourceSurface source L}
    (P : AR3BoundaryMatrixProfile B) (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.anchors.noCutSpecCarrierClaim k

end AR3BoundaryMatrixProfile

structure AR3BoundaryPullbackProfile
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySourceSurface source L)
    (kind : AR3ProfileMatrixKind)
    (κ : Type v) where
  sourceIndexEquiv : B.interface.index ≃ κ
  sourceMatrix : Matrix κ κ ExecComplex
  matrix : Matrix B.interface.index B.interface.index ExecComplex
  matrix_eq_pullback :
    matrix = MatrixTransport.pullback sourceIndexEquiv sourceMatrix
  anchors : AR3BoundaryTransportAnchors B

namespace AR3BoundaryPullbackProfile

variable {source : ArithmeticSource Cell T} {L : Nat}
variable {B : BoundarySourceSurface source L}
variable {kind : AR3ProfileMatrixKind}
variable {κ : Type v}

def fromMatrix
    (B : BoundarySourceSurface source L)
    (kind : AR3ProfileMatrixKind)
    (e : B.interface.index ≃ κ)
    (A : Matrix κ κ ExecComplex) :
    AR3BoundaryPullbackProfile B kind κ where
  sourceIndexEquiv := e
  sourceMatrix := A
  matrix := MatrixTransport.pullback e A
  matrix_eq_pullback := by
    rfl
  anchors := AR3BoundaryTransportAnchors.fromBoundarySource B

theorem component_identity
    (P : AR3BoundaryPullbackProfile B kind κ)
    (i j : B.interface.index) :
    P.matrix i j = P.sourceMatrix (P.sourceIndexEquiv i) (P.sourceIndexEquiv j) := by
  rw [P.matrix_eq_pullback]
  rfl

theorem noCutSpecCarrierClaim_at
    (P : AR3BoundaryPullbackProfile B kind κ)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.anchors.noCutSpecCarrierClaim k

end AR3BoundaryPullbackProfile

structure AR3BoundaryPushforwardProfile
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySourceSurface source L)
    (kind : AR3ProfileMatrixKind)
    (κ : Type v) where
  targetIndexEquiv : B.interface.index ≃ κ
  matrix : Matrix κ κ ExecComplex
  matrix_eq_pushforward :
    matrix = MatrixTransport.pushforward targetIndexEquiv B.interface.matrix
  anchors : AR3BoundaryTransportAnchors B

namespace AR3BoundaryPushforwardProfile

variable {source : ArithmeticSource Cell T} {L : Nat}
variable {B : BoundarySourceSurface source L}
variable {kind : AR3ProfileMatrixKind}
variable {κ : Type v}

def fromBoundarySource
    (B : BoundarySourceSurface source L)
    (kind : AR3ProfileMatrixKind)
    (e : B.interface.index ≃ κ) :
    AR3BoundaryPushforwardProfile B kind κ where
  targetIndexEquiv := e
  matrix := MatrixTransport.pushforward e B.interface.matrix
  matrix_eq_pushforward := by
    rfl
  anchors := AR3BoundaryTransportAnchors.fromBoundarySource B

theorem component_identity
    (P : AR3BoundaryPushforwardProfile B kind κ)
    (i j : κ) :
    P.matrix i j = B.interface.matrix (P.targetIndexEquiv.symm i)
      (P.targetIndexEquiv.symm j) := by
  rw [P.matrix_eq_pushforward]
  rfl

theorem noCutSpecCarrierClaim_at
    (P : AR3BoundaryPushforwardProfile B kind κ)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.anchors.noCutSpecCarrierClaim k

end AR3BoundaryPushforwardProfile

structure AR3MatrixTransportLedger
    (source : ArithmeticSource Cell T) (L : Nat) where
  boundarySource : BoundarySourceSurface source L
  brightBrightSchurProfile : AR3BoundaryMatrixProfile boundarySource
  brightBrightSchurProfile_kind :
    brightBrightSchurProfile.kind = AR3ProfileMatrixKind.brightBrightSchur
  dtnProfile : AR3BoundaryMatrixProfile boundarySource
  dtnProfile_kind : dtnProfile.kind = AR3ProfileMatrixKind.dtn
  charProfile : AR3BoundaryMatrixProfile boundarySource
  charProfile_kind : charProfile.kind = AR3ProfileMatrixKind.char
  route : boundarySource.interface.route = BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    boundarySource.consumptionPolicy = BoundarySourceConsumptionPolicy.boundarySourceOnly
  noFreeBoundaryData : BoundarySourceNoFreeBoundaryData boundarySource.interface

namespace AR3MatrixTransportLedger

variable {source : ArithmeticSource Cell T} {L : Nat}

def fromBoundarySource (B : BoundarySourceSurface source L) :
    AR3MatrixTransportLedger source L where
  boundarySource := B
  brightBrightSchurProfile := AR3BoundaryMatrixProfile.brightBrightSchur B
  brightBrightSchurProfile_kind := by
    rfl
  dtnProfile := AR3BoundaryMatrixProfile.dtn B
  dtnProfile_kind := by
    rfl
  charProfile := AR3BoundaryMatrixProfile.char B
  charProfile_kind := by
    rfl
  route := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  noFreeBoundaryData := B.noFreeBoundaryData

theorem brightBrightSchur_component_identity
    (Ldg : AR3MatrixTransportLedger source L)
    (i j : Ldg.boundarySource.interface.index) :
    Ldg.brightBrightSchurProfile.matrix i j =
      Ldg.boundarySource.interface.matrix i j := by
  exact Ldg.brightBrightSchurProfile.component_identity i j

theorem dtn_component_identity
    (Ldg : AR3MatrixTransportLedger source L)
    (i j : Ldg.boundarySource.interface.index) :
    Ldg.dtnProfile.matrix i j =
      Ldg.boundarySource.interface.matrix i j := by
  exact Ldg.dtnProfile.component_identity i j

theorem char_component_identity
    (Ldg : AR3MatrixTransportLedger source L)
    (i j : Ldg.boundarySource.interface.index) :
    Ldg.charProfile.matrix i j =
      Ldg.boundarySource.interface.matrix i j := by
  exact Ldg.charProfile.component_identity i j

theorem route_recursiveHistory
    (Ldg : AR3MatrixTransportLedger source L) :
    Ldg.boundarySource.interface.route = BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem consumptionPolicy_boundarySourceOnly
    (Ldg : AR3MatrixTransportLedger source L) :
    Ldg.boundarySource.consumptionPolicy =
      BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  Ldg.consumptionPolicy

theorem noCutSpecCarrierClaim_at
    (Ldg : AR3MatrixTransportLedger source L)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noFreeBoundaryData.noCutSpecCarrierClaim k

end AR3MatrixTransportLedger

end BoundarySource

namespace StrengtheningAR3

abbrev AR3ProfileMatrixKind := BoundarySource.AR3ProfileMatrixKind

abbrev AR3BoundaryTransportAnchorsOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface (Cell := Cell) (T := T) source L) :=
  BoundarySource.AR3BoundaryTransportAnchors B

abbrev AR3BoundaryMatrixProfileOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface (Cell := Cell) (T := T) source L) :=
  BoundarySource.AR3BoundaryMatrixProfile B

abbrev AR3BoundaryPullbackProfileOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface (Cell := Cell) (T := T) source L)
    (kind : BoundarySource.AR3ProfileMatrixKind)
    (κ : Type v) :=
  BoundarySource.AR3BoundaryPullbackProfile B kind κ

abbrev AR3BoundaryPushforwardProfileOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface (Cell := Cell) (T := T) source L)
    (kind : BoundarySource.AR3ProfileMatrixKind)
    (κ : Type v) :=
  BoundarySource.AR3BoundaryPushforwardProfile B kind κ

abbrev AR3MatrixTransportLedgerOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.AR3MatrixTransportLedger (Cell := Cell) (T := T) source L

def ar3MatrixTransportLedgerFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    AR3MatrixTransportLedgerOf source L :=
  BoundarySource.AR3MatrixTransportLedger.fromBoundarySource B

theorem ar3MatrixTransportLedger_route
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (ar3MatrixTransportLedgerFromBoundarySource B).boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  BoundarySource.AR3MatrixTransportLedger.route_recursiveHistory
    (ar3MatrixTransportLedgerFromBoundarySource B)

theorem ar3MatrixTransportLedger_consumptionPolicy
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (ar3MatrixTransportLedgerFromBoundarySource B).boundarySource.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly :=
  BoundarySource.AR3MatrixTransportLedger.consumptionPolicy_boundarySourceOnly
    (ar3MatrixTransportLedgerFromBoundarySource B)

end StrengtheningAR3

end CNNA.PillarA.Arithmetic
