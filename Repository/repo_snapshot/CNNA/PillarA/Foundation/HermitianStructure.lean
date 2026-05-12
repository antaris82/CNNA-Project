import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u v

class SeedScalar (𝕜 : Type u) extends CommRing 𝕜, StarRing 𝕜

section MatrixHermitian

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v}

abbrev IsHermitian (A : Matrix ι ι 𝕜) : Prop :=
  A.IsHermitian

structure HermitianMatrix [Fintype ι] [DecidableEq ι] where
  matrix : Matrix ι ι 𝕜
  hermitian : IsHermitian matrix

end MatrixHermitian

namespace HermitianMatrix

section Basic

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

variable (H : HermitianMatrix (𝕜 := 𝕜) (ι := ι))

def carrier : Matrix ι ι 𝕜 :=
  H.matrix

theorem carrier_eq_matrix : H.carrier = H.matrix := by
  rfl

theorem carrier_isHermitian : IsHermitian H.carrier := by
  exact H.hermitian

end Basic

end HermitianMatrix

section MatrixHermitianLemmas

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v}

theorem isHermitian_iff (A : Matrix ι ι 𝕜) :
    IsHermitian A ↔ A.conjTranspose = A := by
  rfl

theorem isHermitian_zero [Fintype ι] :
    IsHermitian (0 : Matrix ι ι 𝕜) := by
  exact Matrix.isHermitian_zero

end MatrixHermitianLemmas

end CNNA.PillarA.Foundation
