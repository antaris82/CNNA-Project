import CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Graph

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive CheegerSeedStatus where
  | finitePillarADiagnosticFromNormalizedGap
  deriving DecidableEq, Repr

inductive CheegerGeometryDisciplineStatus where
  | noContinuousGeometryMetricSpaceOrSpacetimeClaimInPillarA
  deriving DecidableEq, Repr

def cheegerSeedDiagnostic
    {B : BoundarySource.BoundarySourceSurface source L}
    (G : SpectralGapSeed B) : ℚ :=
  G.normalizedGapDiagnostic

structure CheegerSeed
    (B : BoundarySource.BoundarySourceSurface source L) where
  gapSeed : SpectralGapSeed B
  gapSeed_eq : gapSeed = SpectralGapSeed.fromBrightDtNBoundarySource B
  value : ℚ
  value_eq : value = cheegerSeedDiagnostic gapSeed
  status : CheegerSeedStatus
  status_eq : status = CheegerSeedStatus.finitePillarADiagnosticFromNormalizedGap
  geometryDisciplineStatus : CheegerGeometryDisciplineStatus
  geometryDisciplineStatus_eq :
    geometryDisciplineStatus =
      CheegerGeometryDisciplineStatus.noContinuousGeometryMetricSpaceOrSpacetimeClaimInPillarA
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace CheegerSeed

variable {B : BoundarySource.BoundarySourceSurface source L}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L) : CheegerSeed B where
  gapSeed := SpectralGapSeed.fromBrightDtNBoundarySource B
  gapSeed_eq := by
    rfl
  value := cheegerSeedDiagnostic (SpectralGapSeed.fromBrightDtNBoundarySource B)
  value_eq := by
    rfl
  status := CheegerSeedStatus.finitePillarADiagnosticFromNormalizedGap
  status_eq := by
    rfl
  geometryDisciplineStatus :=
    CheegerGeometryDisciplineStatus.noContinuousGeometryMetricSpaceOrSpacetimeClaimInPillarA
  geometryDisciplineStatus_eq := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem value_from_gapSeed
    (C : CheegerSeed B) :
    C.value = cheegerSeedDiagnostic C.gapSeed :=
  C.value_eq

theorem status_closed
    (C : CheegerSeed B) :
    C.status = CheegerSeedStatus.finitePillarADiagnosticFromNormalizedGap :=
  C.status_eq

theorem no_geometry_claim
    (C : CheegerSeed B) :
    C.geometryDisciplineStatus =
      CheegerGeometryDisciplineStatus.noContinuousGeometryMetricSpaceOrSpacetimeClaimInPillarA :=
  C.geometryDisciplineStatus_eq

theorem route_recursiveHistory
    (C : CheegerSeed B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  C.route

theorem noCutSpecCarrierClaim_at
    (C : CheegerSeed B) (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  C.noCutSpecCarrierClaim k

end CheegerSeed

end Graph

namespace StrengtheningAR10b

abbrev AR10bCheegerSeedStatus := Graph.CheegerSeedStatus
abbrev AR10bCheegerGeometryDisciplineStatus := Graph.CheegerGeometryDisciplineStatus

abbrev AR10bCheegerSeed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :=
  Graph.CheegerSeed B

def AR10bCheegerSeedFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    AR10bCheegerSeed B :=
  Graph.CheegerSeed.fromBoundarySource B

theorem AR10bCheegerSeed_status
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    (C : AR10bCheegerSeed B) :
    C.status = Graph.CheegerSeedStatus.finitePillarADiagnosticFromNormalizedGap :=
  Graph.CheegerSeed.status_closed C

theorem AR10bCheegerSeed_no_geometry_claim
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    (C : AR10bCheegerSeed B) :
    C.geometryDisciplineStatus =
      Graph.CheegerGeometryDisciplineStatus.noContinuousGeometryMetricSpaceOrSpacetimeClaimInPillarA :=
  Graph.CheegerSeed.no_geometry_claim C

end StrengtheningAR10b

end CNNA.PillarA.Arithmetic
