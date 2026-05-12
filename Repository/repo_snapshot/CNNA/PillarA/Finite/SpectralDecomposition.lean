import CNNA.PillarA.Finite.SpectralDecompositionCore
import CNNA.PillarA.Finite.ExecSpectral.Certificates

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite.ExecSpectral

universe u

/-
S8f public closure layer for the operative executable spectral root.

`Finite/SpectralDecompositionCore.lean` keeps the green S8a/S8b operative root,
while the visible S8e follow-block remains split into `Finite/ExecSpectral/*`.
This file closes the public operative surface by consuming that explicit follow-block
back into a single proof-carrying API over `ExecComplex`, without reopening the
analytic `ℂ` mirror as a second production surface.
-/
namespace SpectralDecompositionStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev execPolynomialCore (S : SpectralDecompositionStrong Cell T) :
    PolynomialCoreStrong Cell T :=
  PolynomialCoreStrong.ofSpectral S

abbrev execCharpolyCore (S : SpectralDecompositionStrong Cell T) :
    CharpolyCoreStrong Cell T :=
  CharpolyCoreStrong.ofPolynomialCore S.execPolynomialCore

abbrev execRootIsolation (S : SpectralDecompositionStrong Cell T) :
    RootIsolationStrong Cell T :=
  RootIsolationStrong.ofCharpoly S.execCharpolyCore

abbrev execEigenvectorKernel (S : SpectralDecompositionStrong Cell T) :
    EigenvectorKernelStrong Cell T :=
  EigenvectorKernelStrong.ofRootIsolation S.execRootIsolation

abbrev execProjectorCore (S : SpectralDecompositionStrong Cell T) :
    ProjectorCoreStrong Cell T :=
  ProjectorCoreStrong.ofEigenvectorKernel S.execEigenvectorKernel

abbrev execCertificates (S : SpectralDecompositionStrong Cell T) :
    CertificatesStrong Cell T :=
  CertificatesStrong.ofProjectorCore S.execProjectorCore

theorem execPolynomialCore_source_eq (S : SpectralDecompositionStrong Cell T) :
    S.execPolynomialCore.source = S := by
  rfl

theorem execCharpolyCore_source_eq (S : SpectralDecompositionStrong Cell T) :
    S.execCharpolyCore.source = S.execPolynomialCore := by
  rfl

theorem execRootIsolation_source_eq (S : SpectralDecompositionStrong Cell T) :
    S.execRootIsolation.source = S.execCharpolyCore := by
  rfl

theorem execEigenvectorKernel_source_eq (S : SpectralDecompositionStrong Cell T) :
    S.execEigenvectorKernel.source = S.execRootIsolation := by
  rfl

theorem execProjectorCore_source_eq (S : SpectralDecompositionStrong Cell T) :
    S.execProjectorCore.source = S.execEigenvectorKernel := by
  rfl

theorem execCertificates_source_eq (S : SpectralDecompositionStrong Cell T) :
    S.execCertificates.source = S.execProjectorCore := by
  rfl

theorem execCharpolyEval_eq_spectralCharDetEval (S : SpectralDecompositionStrong Cell T) :
    S.execCharpolyCore.charpolyEval = S.spectralCharDetEval := by
  exact S.execCharpolyCore.charpolyEval_eq_spectralCharDetEval

theorem execCoordinateKernelValueQ_eq_degreeQ (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) :
    S.execEigenvectorKernel.coordinateKernelValueQ i = S.degreeQ i := by
  exact S.execEigenvectorKernel.coordinateKernelValueQ_eq_degreeQ i

theorem execCoordinateResidual_eq_coordinateResidual
    (S : SpectralDecompositionStrong Cell T) (i : S.boxVertex) :
    S.execEigenvectorKernel.coordinateResidual i
        (S.execEigenvectorKernel.coordinateKernelValueQ i) =
      S.coordinateSpectralResidual i := by
  exact S.execEigenvectorKernel.coordinateResidual_at_candidate_eq_coordinateResidual i

theorem execProjectorIdempotenceResidual_zero
    (S : SpectralDecompositionStrong Cell T) (i : S.boxVertex) :
    S.execProjectorCore.projectorIdempotenceResidual i = 0 := by
  exact S.execProjectorCore.projectorIdempotenceResidual_zero i

structure CoordinateAlgebraicSpectralPackage (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) where
  interval : RationalInterval
  leftEval : ExecComplex
  rightEval : ExecComplex
  value : ℚ
  witness : S.boxVertex → ExecComplex
  residual : S.boxVertex → ExecComplex
  projector : Matrix S.boxVertex S.boxVertex ExecComplex
  ordered : interval.lower ≤ interval.upper
  center_eq_degreeQ : value = S.degreeQ i
  charpoly_eval_agrees :
    S.execCharpolyCore.charpolyEval value = S.spectralCharDetEval value
  residual_agrees : residual = S.coordinateSpectralResidual i
  projector_hermitian : IsHermitian projector
  projector_idempotenceResidual_zero :
    S.execProjectorCore.projectorIdempotenceResidual i = 0
  projector_selfCommutator_zero :
    S.coordinateProjectorSelfCommutator i = 0

def coordinateAlgebraicSpectralPackage (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) :
    CoordinateAlgebraicSpectralPackage S i δ hδ := by
  let isolation := S.execRootIsolation.coordinateIsolationData i δ hδ
  let kernelCandidate := S.execEigenvectorKernel.coordinateKernelCandidate i
  let execCertificate := S.execCertificates.coordinateExecCertificate i
  refine
    { interval := isolation.interval
      leftEval := isolation.leftEval
      rightEval := isolation.rightEval
      value := kernelCandidate.value
      witness := kernelCandidate.witness
      residual := kernelCandidate.residual
      projector := S.execProjectorCore.coordinateProjector i
      ordered := ?_
      center_eq_degreeQ := ?_
      charpoly_eval_agrees := ?_
      residual_agrees := ?_
      projector_hermitian := ?_
      projector_idempotenceResidual_zero := ?_
      projector_selfCommutator_zero := ?_ }
  · exact (S.execRootIsolation.rootIsolationCertificate i δ hδ).ordered
  · exact S.execEigenvectorKernel.coordinateKernelValueQ_eq_degreeQ i
  · exact execCertificate.charpoly_eval_agrees
  · exact execCertificate.kernel_residual_agrees
  · exact execCertificate.projector_hermitian
  · exact execCertificate.projector_idempotenceResidual_zero
  · exact execCertificate.projector_selfCommutator_zero

structure AlgebraicSpectralPackage (S : SpectralDecompositionStrong Cell T) where
  operativeShadow : SpectralShadow S
  operativeCertificate : SpectralCertificate S
  followBlock : CertificatesStrong Cell T
  charpolyEval : EvalPolynomial
  degreeBound : Nat
  coordinatePackage :
    ∀ i : S.boxVertex, ∀ δ : ℚ, ∀ hδ : 0 ≤ δ,
      CoordinateAlgebraicSpectralPackage S i δ hδ

def algebraicSpectralPackage (S : SpectralDecompositionStrong Cell T) :
    AlgebraicSpectralPackage S where
  operativeShadow := S.spectralShadow
  operativeCertificate := S.spectralCertificate
  followBlock := S.execCertificates
  charpolyEval := S.execCharpolyCore.charpolyEval
  degreeBound := S.execCharpolyCore.degreeBound
  coordinatePackage := fun i δ hδ =>
    S.coordinateAlgebraicSpectralPackage i δ hδ

end SpectralDecompositionStrong

namespace StrengtheningS8f

open CNNA.PillarA.Finite.StrengtheningS8a
open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullAlgebraicSpectralPackage (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    SpectralDecompositionStrong.AlgebraicSpectralPackage
      (referenceFullSpectralDecomposition b p wp) :=
  (referenceFullSpectralDecomposition b p wp).algebraicSpectralPackage

def variationFullAlgebraicSpectralPackage (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    SpectralDecompositionStrong.AlgebraicSpectralPackage
      (variationFullSpectralDecomposition β p wp) :=
  (variationFullSpectralDecomposition β p wp).algebraicSpectralPackage

end StrengtheningS8f

end CNNA.PillarA.Finite
