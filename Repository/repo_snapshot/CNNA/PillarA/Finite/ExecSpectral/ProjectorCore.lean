import CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure ProjectorCoreStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : EigenvectorKernelStrong Cell T

abbrev ProjectorCoreStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ProjectorCoreStrong (Cell := Cell) T

namespace ProjectorCoreStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (P Q : ProjectorCoreStrong Cell T)
    (hsource : P.source = Q.source) :
    P = Q := by
  cases P with
  | mk sourceP =>
    cases Q with
    | mk sourceQ =>
      cases hsource
      rfl

def ofEigenvectorKernel (K : EigenvectorKernelStrong Cell T) :
    ProjectorCoreStrong Cell T where
  source := K

def cast (h : T = U) (P : ProjectorCoreStrong Cell T) :
    ProjectorCoreStrong Cell U := by
  cases h
  exact P

theorem cast_rfl (P : ProjectorCoreStrong Cell T) :
    cast (Cell := Cell) rfl P = P := by
  rfl

abbrev spectral (P : ProjectorCoreStrong Cell T) :=
  P.source.spectral

abbrev boxVertex (P : ProjectorCoreStrong Cell T) :=
  P.spectral.boxVertex

def coordinateProjector (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) : Matrix P.boxVertex P.boxVertex ExecComplex :=
  P.spectral.coordinateProjector i

def projectorIdempotenceResidual (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) : Matrix P.boxVertex P.boxVertex ExecComplex :=
  P.coordinateProjector i * P.coordinateProjector i - P.coordinateProjector i

def projectorKernelCommutator (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) (q : ℚ) :
    Matrix P.boxVertex P.boxVertex ExecComplex :=
  P.coordinateProjector i * P.source.eigenKernelMatrix q -
    P.source.eigenKernelMatrix q * P.coordinateProjector i

theorem coordinateProjector_isHermitian (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) :
    IsHermitian (P.coordinateProjector i) := by
  exact P.spectral.coordinateProjector_isHermitian i

theorem coordinateProjector_mul_self (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) :
    P.coordinateProjector i * P.coordinateProjector i = P.coordinateProjector i := by
  apply Matrix.ext
  intro j k
  by_cases hj : j = i <;> by_cases hk : k = i
  · subst j
    subst k
    simp [Matrix.mul_apply, coordinateProjector,
      SpectralDecompositionStrong.coordinateProjector]
  · subst j
    simp [Matrix.mul_apply, coordinateProjector,
      SpectralDecompositionStrong.coordinateProjector, hk]
  · subst k
    simp [Matrix.mul_apply, coordinateProjector,
      SpectralDecompositionStrong.coordinateProjector, hj]
  · simp [Matrix.mul_apply, coordinateProjector,
      SpectralDecompositionStrong.coordinateProjector, hj, hk]

theorem projectorIdempotenceResidual_zero (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) :
    P.projectorIdempotenceResidual i = 0 := by
  unfold projectorIdempotenceResidual
  rw [P.coordinateProjector_mul_self i]
  simp

theorem coordinateProjector_selfCommutator_zero (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) :
    P.spectral.coordinateProjectorSelfCommutator i = 0 := by
  exact P.spectral.coordinateProjector_selfCommutator_zero i

structure ProjectorCertificate (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) where
  hermitian : IsHermitian (P.coordinateProjector i)
  idempotenceResidual_zero : P.projectorIdempotenceResidual i = 0
  selfCommutator_zero : P.spectral.coordinateProjectorSelfCommutator i = 0


def projectorCertificate (P : ProjectorCoreStrong Cell T)
    (i : P.boxVertex) : ProjectorCertificate P i where
  hermitian := P.coordinateProjector_isHermitian i
  idempotenceResidual_zero := P.projectorIdempotenceResidual_zero i
  selfCommutator_zero := P.coordinateProjector_selfCommutator_zero i

end ProjectorCoreStrong

end CNNA.PillarA.Finite.ExecSpectral
