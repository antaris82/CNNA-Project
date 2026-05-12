import CNNA.PillarA.Foundation.Notation
import CNNA.PillarA.ToC.Notation
import CNNA.PillarA.Finite.Notation
import CNNA.PillarA.DtN.Notation
import CNNA.PillarA.Sectors.Notation
import CNNA.PillarA.Closure.Notation
import CNNA.PillarA.Network.Notation
import CNNA.PillarA.Geometry.Notation
import CNNA.PillarA.Coupling.Notation
import CNNA.PillarA.Arithmetic.Notation
import CNNA.PillarA.Handoff.Notation

set_option autoImplicit false

namespace CNNA.PillarA

universe u v

abbrev RootLayer (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.Foundation.SubstrateClass.rootLayer (Cell := Cell)

abbrev ParentRel
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (c : Cell (L + 1)) (p : Cell L) : Prop :=
  CNNA.PillarA.Foundation.SubstrateClass.ParentRel (Cell := Cell) c p

abbrev ChildRel
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (p : Cell L) (c : Cell (L + 1)) : Prop :=
  CNNA.PillarA.Foundation.SubstrateClass.ChildRel (Cell := Cell) p c

abbrev RefineSet
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (S : Finset (Cell L)) : Finset (Cell (L + 1)) :=
  CNNA.PillarA.Foundation.SubstrateClass.refineSet (Cell := Cell) S

abbrev CoarsenSet
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (S : Finset (Cell (L + 1))) : Finset (Cell L) :=
  CNNA.PillarA.Foundation.SubstrateClass.coarsenSet (Cell := Cell) S

abbrev InfiniteThread (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.Foundation.InfiniteThread Cell

abbrev LevelVariableCell
    (branching : Nat → Nat) (L : Nat) :=
  CNNA.PillarA.Foundation.LevelVariableSubstrate.LevelVariableCell branching L

abbrev ThermalAxis :=
  CNNA.PillarA.Foundation.ThermalAxis

abbrev WeightPolicy :=
  CNNA.PillarA.Foundation.WeightPolicy

abbrev RegularizationPolicy :=
  CNNA.PillarA.Foundation.RegularizationPolicy

abbrev LevelUniformBranchingSubstrate
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.Foundation.LevelUniformBranchingSubstrateClass Cell

abbrev UniformBranchingSubstrate
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.Foundation.UniformBranchingSubstrateClass Cell

abbrev IdealToCFamily (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.DirectedFamily (Cell := Cell)

abbrev IdealToCThread (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.IdealThread Cell

abbrev LayerSlice (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.Foundation.LayerSlice Cell

abbrev BoundarySlice (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.Foundation.BoundarySlice Cell

abbrev RootSlice (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.rootSlice (Cell := Cell)

abbrev EmptyOrigin (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.emptyOrigin (Cell := Cell)

abbrev ParentSlice
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (c : Cell (L + 1)) :=
  CNNA.PillarA.ToC.parentSlice (Cell := Cell) c

abbrev ChildSlice
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] {L : Nat}
    (c : Cell L) :=
  CNNA.PillarA.ToC.childSlice (Cell := Cell) c

abbrev AddressPresentation
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.AddressPresentation Cell Addr

abbrev AddressFamily
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.ToC.AddressPresentation.AddressFamily (Cell := Cell) (Addr := Addr)

abbrev AddressThread
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.ToC.AddressPresentation.AddressThread (Cell := Cell) (Addr := Addr)

abbrev ReferenceIdealCell
    (b : Nat) (L : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.ReferenceCell b L

abbrev ReferenceIdealAddr
    (b : Nat) (L : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.ReferenceAddr b L

abbrev ReferenceIdealThread
    (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceThread b

abbrev ReferenceIdealFamily
    (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceFamily b

abbrev ReferenceAddressThread
    (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceAddressThread b

abbrev ReferenceAddressFamily
    (b : Nat) :=
  CNNA.PillarA.ToC.ConcreteIdeal.referenceAddressFamily b

abbrev VariationIdealCell
    (β : Nat → Nat) (L : Nat) :=
  CNNA.PillarA.ToC.VariationIdealCellOf β L

abbrev VariationIdealThread
    (β : Nat → Nat) :=
  CNNA.PillarA.ToC.variationThread β

abbrev VariationIdealFamily
    (β : Nat → Nat) :=
  CNNA.PillarA.ToC.variationFamily β

abbrev ConcretePolicy :=
  CNNA.PillarA.ToC.ConcretePolicy

abbrev TruncatedFamily
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.TruncatedFamily Cell

abbrev ToCStrong
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell] :=
  CNNA.PillarA.ToC.ToCStrong Cell

abbrev FiniteApproximant
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ApproximantStrong (Cell := Cell) T

abbrev FiniteSelection
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.SelectionStrong (Cell := Cell) T

abbrev FiniteDirichletLaplacian
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.DirichletLaplacianStrong (Cell := Cell) T

abbrev FiniteSpectralDecomposition
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong (Cell := Cell) T

abbrev FiniteSpectralDecompositionC
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.SpectralDecompositionCStrong (Cell := Cell) T

abbrev FiniteSpectralBridge
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.SpectralBridgeStrong (Cell := Cell) T

abbrev SpectralShadowOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (S : CNNA.PillarA.Finite.SpectralDecompositionStrong Cell T) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong.SpectralShadow S

abbrev SpectralCertificateOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (S : CNNA.PillarA.Finite.SpectralDecompositionStrong Cell T) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong.SpectralCertificate S

abbrev CoordinateSpectralCandidateOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (S : CNNA.PillarA.Finite.SpectralDecompositionStrong Cell T) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong.CoordinateSpectralCandidate S

abbrev CoordinateProjectorCertificateOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (S : CNNA.PillarA.Finite.SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong.CoordinateProjectorCertificate S i

abbrev CoordinateAlgebraicSpectralPackageOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (S : CNNA.PillarA.Finite.SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong.CoordinateAlgebraicSpectralPackage S i δ hδ

abbrev AlgebraicSpectralPackageOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (S : CNNA.PillarA.Finite.SpectralDecompositionStrong Cell T) :=
  CNNA.PillarA.Finite.SpectralDecompositionStrong.AlgebraicSpectralPackage S


abbrev FinitePolynomialCore
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ExecSpectral.PolynomialCoreStrong (Cell := Cell) T

abbrev FiniteCharpolyCore
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ExecSpectral.CharpolyCoreStrong (Cell := Cell) T

abbrev FiniteRootIsolation
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ExecSpectral.RootIsolationStrong (Cell := Cell) T

abbrev FiniteEigenvectorKernel
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernelStrong (Cell := Cell) T

abbrev FiniteProjectorCore
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ExecSpectral.ProjectorCoreStrong (Cell := Cell) T

abbrev FiniteExecSpectralCertificates
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ExecSpectral.CertificatesStrong (Cell := Cell) T

abbrev FiniteStateSpaceSeed
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.StateSpaceStrong (Cell := Cell) T

abbrev FiniteMatrixExponential
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.MatrixExponentialStrong (Cell := Cell) T

abbrev FiniteGibbsStateSeed
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.GibbsStateSeedStrong (Cell := Cell) T

abbrev FiniteGibbsApproxPartitionWitness
    {Cell : Nat → Type u} [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (G : CNNA.PillarA.Finite.GibbsStateSeedStrong (Cell := Cell) T)
    (N : Nat) :=
  CNNA.PillarA.Finite.GibbsStateSeedStrong.GibbsApproxPartitionWitness G N

abbrev FiniteEvolutionApproxAxis :=
  CNNA.PillarA.Finite.EvolutionApproxAxis

abbrev FiniteUnitaryEvolution
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.UnitaryEvolutionStrong (Cell := Cell) T

abbrev FiniteDynamicsAdapter
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.DynamicsAdapterStrong (Cell := Cell) T

abbrev FiniteStarAlgDynamicsSeed
    {Cell : Nat → Type u} [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (D : CNNA.PillarA.Finite.DynamicsAdapterStrong (Cell := Cell) T)
    (Ξ : CNNA.PillarA.Finite.EvolutionApproxAxis) :=
  CNNA.PillarA.Finite.DynamicsAdapterStrong.StarAlgDynamicsSeed D Ξ

abbrev FiniteChannelSeed
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Finite.ChannelSeedStrong (Cell := Cell) T

abbrev FiniteKrausFamily
    {Cell : Nat → Type u} [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (C : CNNA.PillarA.Finite.ChannelSeedStrong (Cell := Cell) T) :=
  CNNA.PillarA.Finite.ChannelSeedStrong.KrausFamily C

abbrev FiniteUnitarySingleKrausSeed
    {Cell : Nat → Type u} [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (C : CNNA.PillarA.Finite.ChannelSeedStrong (Cell := Cell) T) :=
  CNNA.PillarA.Finite.ChannelSeedStrong.UnitarySingleKrausSeed C

abbrev FiniteAlgebraicChannelPackage
    {Cell : Nat → Type u} [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (C : CNNA.PillarA.Finite.ChannelSeedStrong (Cell := Cell) T) :=
  CNNA.PillarA.Finite.ChannelSeedStrong.AlgebraicChannelPackage C


abbrev BinaryDtN
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.DtN.DtNStrong (Cell := Cell) T

abbrev BinaryInteriorEliminationMode :=
  CNNA.PillarA.DtN.InteriorEliminationMode

abbrev BinaryInteriorSolve
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStrong Cell T) :=
  K.interiorSolve

abbrev BinaryBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStrong Cell T) :=
  K.boundaryOperator


abbrev StabilizedBinaryDtN
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.DtN.DtNStabilizedStrong (Cell := Cell) T

abbrev RawBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.rawBoundaryOperator

abbrev SymmetrizedBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.symmetrizedBoundaryOperator

abbrev StabilizedBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.stabilizedOperator

abbrev StabilizedSymmetricBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.stabilizedSymmetricOperator

abbrev BranchPatch
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.BranchPatchStrong (Cell := Cell) T

abbrev ComplementSectorFamily
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.ComplementSectorFamilyStrong (Cell := Cell) T


abbrev SectorSplit
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.SectorSplitStrong (Cell := Cell) T

abbrev BranchingWitness
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.BranchingWitnessStrong (Cell := Cell) T

abbrev SelectedBranching
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.SelectedBranchingStrong (Cell := Cell) T


abbrev UVSpectralSelector
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.UVSpectralSelectorStrong (Cell := Cell) T

abbrev BranchingSelector
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.BranchingSelectorStrong (Cell := Cell) T

abbrev ParameterClosure
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Closure.ParameterClosureStrong (Cell := Cell) T

abbrev RegularizationClosure
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Closure.RegularizationClosureStrong (Cell := Cell) T

abbrev RegionNet
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.RegionNetStrong (Cell := Cell) T

abbrev InfiniteCarrier
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.InfiniteCarrierStrong (Cell := Cell) T

abbrev SectorChannels
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.SectorChannelsStrong (Cell := Cell) T

abbrev SectorSysEnv
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.SectorSysEnvStrong (Cell := Cell) T

abbrev RelativeEntropyFlow
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.RelativeEntropyFlowStrong (Cell := Cell) T

abbrev RegionKind :=
  CNNA.PillarA.Network.RegionKind

abbrev SysEnvKind :=
  CNNA.PillarA.Network.SysEnvKind

abbrev BundledAddress
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.BundledAddress (Cell := Cell) (Addr := Addr)

abbrev AddressWorldline
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.Worldline (Cell := Cell) (Addr := Addr)

abbrev AddressWorldTube
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr] :=
  CNNA.PillarA.Geometry.WorldTube (Cell := Cell) (Addr := Addr)

abbrev GeneralizedDtN
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Coupling.GeneralizedDtNStrong (Cell := Cell) T

abbrev CoupledSectorKind :=
  CNNA.PillarA.Coupling.CoupledSectorKind


abbrev SectorExport
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.SectorExportStrong (Cell := Cell) T


abbrev Step1StrongCore
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.Step1StrongCore (Cell := Cell) T

abbrev Step1MathData
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.Step1MathDataStrong (Cell := Cell) T

abbrev ABHandoffStrong
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.ABHandoffStrong (Cell := Cell) T

abbrev PillarAStep1Closed
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.PillarAStep1Closed (Cell := Cell) T

abbrev MultiSchur
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Coupling.MultiSchurStrong (Cell := Cell) T

abbrev Prefix
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [CNNA.PillarA.Foundation.SubstrateClass Cell]
    [CNNA.PillarA.ToC.AddressPresentation Cell Addr]
    {L M : Nat} (a : Addr L) (b : Addr M) : Prop :=
  CNNA.PillarA.ToC.AddressPresentation.PrefixRel Cell Addr a b

end CNNA.PillarA
