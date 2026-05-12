import CNNA.PillarA.Finite.Selection
import CNNA.PillarA.Finite.DirichletLaplacian
import CNNA.PillarA.Finite.SpectralDecomposition
import CNNA.PillarA.Finite.SpectralDecompositionC
import CNNA.PillarA.Finite.SpectralBridge
import CNNA.PillarA.Finite.ExecSpectral.Notation
import CNNA.PillarA.Finite.StateSpace
import CNNA.PillarA.Finite.MatrixExponential
import CNNA.PillarA.Finite.GibbsStateSeed
import CNNA.PillarA.Finite.UnitaryEvolution
import CNNA.PillarA.Finite.DynamicsAdapter
import CNNA.PillarA.Finite.ChannelSeed

set_option autoImplicit false

namespace CNNA.PillarA.Finite

universe u

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

abbrev DirichletWeightOf
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (A : CNNA.PillarA.Finite.ApproximantStrong Cell T) :=
  CNNA.PillarA.Finite.DirichletWeight (Cell := Cell) A

abbrev DirichletBoxVertex
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (A : CNNA.PillarA.Finite.ApproximantStrong Cell T) :=
  CNNA.PillarA.Finite.BoxVertex (Cell := Cell) A

abbrev DirichletBoundaryVertex
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (A : CNNA.PillarA.Finite.ApproximantStrong Cell T) :=
  CNNA.PillarA.Finite.BoundaryVertex (Cell := Cell) A

abbrev DirichletInteriorVertex
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (A : CNNA.PillarA.Finite.ApproximantStrong Cell T) :=
  CNNA.PillarA.Finite.InteriorVertex (Cell := Cell) A


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

end CNNA.PillarA.Finite
