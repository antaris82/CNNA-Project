import CNNA.PillarA.Arithmetic.Schur.IdentityLedger

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Graph

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive GapMatrixKind where
  | adjacency
  | laplacian
  | brightDtN
  | schur
  deriving DecidableEq, Repr

inductive SpectralGapSeedStatus where
  | derivedFromBoundaryMatrixDiagnostic
  deriving DecidableEq, Repr

inductive NormalizedGapSeedStatus where
  | normalizedByLevelHistoryCardinality
  deriving DecidableEq, Repr

inductive GapNoPhysicalInterpretationStatus where
  | pillarADiagnosticOnlyNoDecoherenceThermalTimeSpacetimeOrGeometryClaim
  deriving DecidableEq, Repr

def boundaryRootDiagonalRe
    (B : BoundarySource.BoundarySourceSurface source L) : ℚ :=
  (Schur.boundaryLevelHistoryMatrix B (Schur.rootIndex L) (Schur.rootIndex L)).re

def boundaryLeafDiagonalRe
    (B : BoundarySource.BoundarySourceSurface source L) : ℚ :=
  (Schur.boundaryLevelHistoryMatrix B (Schur.leafIndex L) (Schur.leafIndex L)).re

def boundaryEndpointGapDiagnostic
    (B : BoundarySource.BoundarySourceSurface source L) : ℚ :=
  boundaryLeafDiagonalRe B - boundaryRootDiagonalRe B

def boundaryNormalizedGapDiagnostic
    (B : BoundarySource.BoundarySourceSurface source L) : ℚ :=
  boundaryEndpointGapDiagnostic B / ((L + 1 : Nat) : ℚ)

structure SpectralGapSeed
    (B : BoundarySource.BoundarySourceSurface source L) where
  matrixKind : GapMatrixKind
  matrix : BoundarySource.LevelHistoryMatrix L
  matrix_eq_boundary : matrix = Schur.boundaryLevelHistoryMatrix B
  rootDiagonalRe : ℚ
  rootDiagonalRe_eq : rootDiagonalRe = boundaryRootDiagonalRe B
  leafDiagonalRe : ℚ
  leafDiagonalRe_eq : leafDiagonalRe = boundaryLeafDiagonalRe B
  gapDiagnostic : ℚ
  gapDiagnostic_eq : gapDiagnostic = boundaryEndpointGapDiagnostic B
  normalizedGapDiagnostic : ℚ
  normalizedGapDiagnostic_eq :
    normalizedGapDiagnostic = boundaryNormalizedGapDiagnostic B
  gapStatus : SpectralGapSeedStatus
  gapStatus_eq :
    gapStatus = SpectralGapSeedStatus.derivedFromBoundaryMatrixDiagnostic
  normalizedStatus : NormalizedGapSeedStatus
  normalizedStatus_eq :
    normalizedStatus = NormalizedGapSeedStatus.normalizedByLevelHistoryCardinality
  noPhysicalInterpretationStatus : GapNoPhysicalInterpretationStatus
  noPhysicalInterpretationStatus_eq :
    noPhysicalInterpretationStatus =
      GapNoPhysicalInterpretationStatus.pillarADiagnosticOnlyNoDecoherenceThermalTimeSpacetimeOrGeometryClaim
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace SpectralGapSeed

variable {B : BoundarySource.BoundarySourceSurface source L}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (kind : GapMatrixKind) : SpectralGapSeed B where
  matrixKind := kind
  matrix := Schur.boundaryLevelHistoryMatrix B
  matrix_eq_boundary := by
    rfl
  rootDiagonalRe := boundaryRootDiagonalRe B
  rootDiagonalRe_eq := by
    rfl
  leafDiagonalRe := boundaryLeafDiagonalRe B
  leafDiagonalRe_eq := by
    rfl
  gapDiagnostic := boundaryEndpointGapDiagnostic B
  gapDiagnostic_eq := by
    rfl
  normalizedGapDiagnostic := boundaryNormalizedGapDiagnostic B
  normalizedGapDiagnostic_eq := by
    rfl
  gapStatus := SpectralGapSeedStatus.derivedFromBoundaryMatrixDiagnostic
  gapStatus_eq := by
    rfl
  normalizedStatus := NormalizedGapSeedStatus.normalizedByLevelHistoryCardinality
  normalizedStatus_eq := by
    rfl
  noPhysicalInterpretationStatus :=
    GapNoPhysicalInterpretationStatus.pillarADiagnosticOnlyNoDecoherenceThermalTimeSpacetimeOrGeometryClaim
  noPhysicalInterpretationStatus_eq := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

def fromBrightDtNBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L) : SpectralGapSeed B :=
  fromBoundarySource B GapMatrixKind.brightDtN

def fromSchurBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L) : SpectralGapSeed B :=
  fromBoundarySource B GapMatrixKind.schur

theorem matrix_from_boundary
    (G : SpectralGapSeed B) :
    G.matrix = Schur.boundaryLevelHistoryMatrix B :=
  G.matrix_eq_boundary

theorem rootDiagonalRe_from_boundary
    (G : SpectralGapSeed B) :
    G.rootDiagonalRe = boundaryRootDiagonalRe B :=
  G.rootDiagonalRe_eq

theorem leafDiagonalRe_from_boundary
    (G : SpectralGapSeed B) :
    G.leafDiagonalRe = boundaryLeafDiagonalRe B :=
  G.leafDiagonalRe_eq

theorem gapDiagnostic_from_boundary
    (G : SpectralGapSeed B) :
    G.gapDiagnostic = boundaryEndpointGapDiagnostic B :=
  G.gapDiagnostic_eq

theorem normalizedGapDiagnostic_from_boundary
    (G : SpectralGapSeed B) :
    G.normalizedGapDiagnostic = boundaryNormalizedGapDiagnostic B :=
  G.normalizedGapDiagnostic_eq

theorem gap_status_closed
    (G : SpectralGapSeed B) :
    G.gapStatus = SpectralGapSeedStatus.derivedFromBoundaryMatrixDiagnostic :=
  G.gapStatus_eq

theorem normalized_status_closed
    (G : SpectralGapSeed B) :
    G.normalizedStatus = NormalizedGapSeedStatus.normalizedByLevelHistoryCardinality :=
  G.normalizedStatus_eq

theorem no_physical_interpretation
    (G : SpectralGapSeed B) :
    G.noPhysicalInterpretationStatus =
      GapNoPhysicalInterpretationStatus.pillarADiagnosticOnlyNoDecoherenceThermalTimeSpacetimeOrGeometryClaim :=
  G.noPhysicalInterpretationStatus_eq

theorem route_recursiveHistory
    (G : SpectralGapSeed B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  G.route

theorem noCutSpecCarrierClaim_at
    (G : SpectralGapSeed B) (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  G.noCutSpecCarrierClaim k

end SpectralGapSeed

end Graph

namespace StrengtheningAR10b

abbrev AR10bGapMatrixKind := Graph.GapMatrixKind
abbrev AR10bSpectralGapSeedStatus := Graph.SpectralGapSeedStatus
abbrev AR10bNormalizedGapSeedStatus := Graph.NormalizedGapSeedStatus
abbrev AR10bGapNoPhysicalInterpretationStatus :=
  Graph.GapNoPhysicalInterpretationStatus

abbrev AR10bSpectralGapSeed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :=
  Graph.SpectralGapSeed B

def AR10bSpectralGapSeedFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (kind : Graph.GapMatrixKind) :
    AR10bSpectralGapSeed B :=
  Graph.SpectralGapSeed.fromBoundarySource B kind

def AR10bBrightDtNGapSeedFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    AR10bSpectralGapSeed B :=
  Graph.SpectralGapSeed.fromBrightDtNBoundarySource B

theorem AR10bSpectralGapSeed_gap_status
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    (G : AR10bSpectralGapSeed B) :
    G.gapStatus = Graph.SpectralGapSeedStatus.derivedFromBoundaryMatrixDiagnostic :=
  Graph.SpectralGapSeed.gap_status_closed G

theorem AR10bSpectralGapSeed_no_physical_interpretation
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    (G : AR10bSpectralGapSeed B) :
    G.noPhysicalInterpretationStatus =
      Graph.GapNoPhysicalInterpretationStatus.pillarADiagnosticOnlyNoDecoherenceThermalTimeSpacetimeOrGeometryClaim :=
  Graph.SpectralGapSeed.no_physical_interpretation G

end StrengtheningAR10b

end CNNA.PillarA.Arithmetic
