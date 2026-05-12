import CNNA.PillarA.Finite.ExecSpectral.BuildAll

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

universe u

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

end CNNA.PillarA.Finite.ExecSpectral
