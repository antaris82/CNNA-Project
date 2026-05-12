import CNNA.PillarA.Finite.ExecSpectral.ProjectorCore

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure CertificatesStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : ProjectorCoreStrong Cell T

abbrev CertificatesStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CertificatesStrong (Cell := Cell) T

namespace CertificatesStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (C D : CertificatesStrong Cell T)
    (hsource : C.source = D.source) :
    C = D := by
  cases C with
  | mk sourceC =>
    cases D with
    | mk sourceD =>
      cases hsource
      rfl

def ofProjectorCore (P : ProjectorCoreStrong Cell T) :
    CertificatesStrong Cell T where
  source := P

def cast (h : T = U) (C : CertificatesStrong Cell T) :
    CertificatesStrong Cell U := by
  cases h
  exact C

theorem cast_rfl (C : CertificatesStrong Cell T) :
    cast (Cell := Cell) rfl C = C := by
  rfl

abbrev projector (C : CertificatesStrong Cell T) :=
  C.source

abbrev kernel (C : CertificatesStrong Cell T) :=
  C.projector.source

abbrev rootIsolation (C : CertificatesStrong Cell T) :=
  C.kernel.source

abbrev charpoly (C : CertificatesStrong Cell T) :=
  C.rootIsolation.source

abbrev polynomial (C : CertificatesStrong Cell T) :=
  C.charpoly.source

abbrev spectral (C : CertificatesStrong Cell T) :=
  C.polynomial.source

abbrev boxVertex (C : CertificatesStrong Cell T) :=
  C.spectral.boxVertex

structure CoordinateExecCertificate (C : CertificatesStrong Cell T)
    (i : C.boxVertex) where
  charpoly_eval_agrees :
    C.charpoly.charpolyEval (C.kernel.coordinateKernelValueQ i) =
      C.spectral.spectralCharDetEval (C.kernel.coordinateKernelValueQ i)
  kernel_residual_agrees :
    C.kernel.coordinateResidual i (C.kernel.coordinateKernelValueQ i) =
      C.spectral.coordinateSpectralResidual i
  projector_hermitian :
    IsHermitian (C.projector.coordinateProjector i)
  projector_idempotenceResidual_zero :
    C.projector.projectorIdempotenceResidual i = 0
  projector_selfCommutator_zero :
    C.spectral.coordinateProjectorSelfCommutator i = 0


def coordinateExecCertificate (C : CertificatesStrong Cell T)
    (i : C.boxVertex) : CoordinateExecCertificate C i where
  charpoly_eval_agrees := by
    have h := congrArg (fun f => f (C.kernel.coordinateKernelValueQ i))
      C.charpoly.charpolyEval_eq_spectralCharDetEval
    exact h
  kernel_residual_agrees :=
    C.kernel.coordinateResidual_at_candidate_eq_coordinateResidual i
  projector_hermitian :=
    C.projector.coordinateProjector_isHermitian i
  projector_idempotenceResidual_zero :=
    C.projector.projectorIdempotenceResidual_zero i
  projector_selfCommutator_zero :=
    C.projector.coordinateProjector_selfCommutator_zero i

end CertificatesStrong

namespace StrengtheningS8e

open CNNA.PillarA.Finite.StrengtheningS8a
open CNNA.PillarA.Finite.StrengtheningS5


def referenceFullPolynomialCore (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    PolynomialCoreStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  PolynomialCoreStrong.ofSpectral (referenceFullSpectralDecomposition b p wp)


def variationFullPolynomialCore (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    PolynomialCoreStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  PolynomialCoreStrong.ofSpectral (variationFullSpectralDecomposition β p wp)


def referenceFullCharpolyCore (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    CharpolyCoreStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  CharpolyCoreStrong.ofPolynomialCore (referenceFullPolynomialCore b p wp)


def variationFullCharpolyCore (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    CharpolyCoreStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  CharpolyCoreStrong.ofPolynomialCore (variationFullPolynomialCore β p wp)


def referenceFullRootIsolation (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    RootIsolationStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  RootIsolationStrong.ofCharpoly (referenceFullCharpolyCore b p wp)


def variationFullRootIsolation (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    RootIsolationStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  RootIsolationStrong.ofCharpoly (variationFullCharpolyCore β p wp)


def referenceFullEigenvectorKernel (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    EigenvectorKernelStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  EigenvectorKernelStrong.ofRootIsolation (referenceFullRootIsolation b p wp)


def variationFullEigenvectorKernel (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    EigenvectorKernelStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  EigenvectorKernelStrong.ofRootIsolation (variationFullRootIsolation β p wp)


def referenceFullProjectorCore (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    ProjectorCoreStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  ProjectorCoreStrong.ofEigenvectorKernel (referenceFullEigenvectorKernel b p wp)


def variationFullProjectorCore (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    ProjectorCoreStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  ProjectorCoreStrong.ofEigenvectorKernel (variationFullEigenvectorKernel β p wp)


def referenceFullExecSpectralCertificates (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    CertificatesStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  CertificatesStrong.ofProjectorCore (referenceFullProjectorCore b p wp)


def variationFullExecSpectralCertificates (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    CertificatesStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  CertificatesStrong.ofProjectorCore (variationFullProjectorCore β p wp)

end StrengtheningS8e

end CNNA.PillarA.Finite.ExecSpectral
