import CNNA.PillarA.Finite.ExecSpectral.RootIsolation

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure EigenvectorKernelStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : RootIsolationStrong Cell T

abbrev EigenvectorKernelStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  EigenvectorKernelStrong (Cell := Cell) T

namespace EigenvectorKernelStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (K L : EigenvectorKernelStrong Cell T)
    (hsource : K.source = L.source) :
    K = L := by
  cases K with
  | mk sourceK =>
    cases L with
    | mk sourceL =>
      cases hsource
      rfl

def ofRootIsolation (R : RootIsolationStrong Cell T) :
    EigenvectorKernelStrong Cell T where
  source := R

def cast (h : T = U) (K : EigenvectorKernelStrong Cell T) :
    EigenvectorKernelStrong Cell U := by
  cases h
  exact K

theorem cast_rfl (K : EigenvectorKernelStrong Cell T) :
    cast (Cell := Cell) rfl K = K := by
  rfl

abbrev spectral (K : EigenvectorKernelStrong Cell T) :=
  K.source.spectral

abbrev boxVertex (K : EigenvectorKernelStrong Cell T) :=
  K.spectral.boxVertex

def eigenKernelMatrix (K : EigenvectorKernelStrong Cell T) (q : ℚ) :
    Matrix K.boxVertex K.boxVertex ExecComplex :=
  fun i j =>
    if i = j then
      K.spectral.execMatrix i j - ExecComplex.ofRat q
    else
      K.spectral.execMatrix i j

def coordinateWitness (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) : K.boxVertex → ExecComplex :=
  Pi.single i 1

def coordinateResidual (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) (q : ℚ) : K.boxVertex → ExecComplex :=
  (K.eigenKernelMatrix q).mulVec (K.coordinateWitness i)

def coordinateKernelValueQ (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) : ℚ :=
  K.source.coordinateCenter i

structure KernelCandidate (K : EigenvectorKernelStrong Cell T) where
  value : ℚ
  witness : K.boxVertex → ExecComplex
  residual : K.boxVertex → ExecComplex


def coordinateKernelCandidate (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) : KernelCandidate K where
  value := K.coordinateKernelValueQ i
  witness := K.coordinateWitness i
  residual := K.coordinateResidual i (K.coordinateKernelValueQ i)

theorem coordinateKernelValueQ_eq_degreeQ (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) :
    K.coordinateKernelValueQ i = K.spectral.degreeQ i := by
  exact K.source.coordinateCenter_eq_degreeQ i

theorem coordinateResidual_apply (K : EigenvectorKernelStrong Cell T)
    (i j : K.boxVertex) (q : ℚ) :
    K.coordinateResidual i q j = K.eigenKernelMatrix q j i := by
  unfold coordinateResidual coordinateWitness
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem coordinateResidual_at_candidate_eq_coordinateResidual
    (K : EigenvectorKernelStrong Cell T) (i : K.boxVertex) :
    K.coordinateResidual i (K.coordinateKernelValueQ i) =
      K.spectral.coordinateSpectralResidual i := by
  funext j
  by_cases hji : j = i
  · subst hji
    rw [coordinateResidual_apply]
    unfold eigenKernelMatrix SpectralDecompositionStrong.coordinateSpectralResidual
    rw [if_pos rfl, if_pos rfl]
    rw [K.coordinateKernelValueQ_eq_degreeQ]
    rw [K.spectral.execMatrix_apply_diag]
    apply ExecComplex.ext
    · simp
    · simp
  · rw [coordinateResidual_apply]
    unfold eigenKernelMatrix SpectralDecompositionStrong.coordinateSpectralResidual
    rw [if_neg hji, if_neg hji]

structure EigenvectorKernelCertificate (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) where
  value_eq_degreeQ : K.coordinateKernelValueQ i = K.spectral.degreeQ i
  residual_eq_coordinateResidual :
    K.coordinateResidual i (K.coordinateKernelValueQ i) =
      K.spectral.coordinateSpectralResidual i


def eigenvectorKernelCertificate (K : EigenvectorKernelStrong Cell T)
    (i : K.boxVertex) : EigenvectorKernelCertificate K i where
  value_eq_degreeQ := K.coordinateKernelValueQ_eq_degreeQ i
  residual_eq_coordinateResidual :=
    K.coordinateResidual_at_candidate_eq_coordinateResidual i

end EigenvectorKernelStrong

end CNNA.PillarA.Finite.ExecSpectral
