import Mathlib.Algebra.BigOperators.Ring.Finset
import CNNA.PillarA.Foundation.HermitianStructure

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Foundation

universe u v

abbrev StateVector (𝕜 : Type u) (ι : Type v) : Type (max u v) :=
  ι → 𝕜

abbrev FiniteStateSpace (𝕜 : Type u) (ι : Type v) : Type (max u v) :=
  StateVector 𝕜 ι

section SesquilinearSeed

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v} [Fintype ι]

def sesq (v w : StateVector 𝕜 ι) : 𝕜 :=
  ∑ i : ι, star (v i) * w i

theorem sesq_def (v w : StateVector 𝕜 ι) :
    sesq v w = ∑ i : ι, star (v i) * w i := by
  rfl

theorem sesq_zero_left (w : StateVector 𝕜 ι) :
    sesq (𝕜 := 𝕜) (ι := ι) 0 w = 0 := by
  simp [sesq]

theorem sesq_zero_right (v : StateVector 𝕜 ι) :
    sesq (𝕜 := 𝕜) (ι := ι) v 0 = 0 := by
  simp [sesq]

theorem sesq_add_left (u v w : StateVector 𝕜 ι) :
    sesq (𝕜 := 𝕜) (ι := ι) (u + v) w =
      sesq (𝕜 := 𝕜) (ι := ι) u w + sesq (𝕜 := 𝕜) (ι := ι) v w := by
  simp [sesq, Finset.sum_add_distrib, star_add, add_mul]

theorem sesq_add_right (u v w : StateVector 𝕜 ι) :
    sesq (𝕜 := 𝕜) (ι := ι) u (v + w) =
      sesq (𝕜 := 𝕜) (ι := ι) u v + sesq (𝕜 := 𝕜) (ι := ι) u w := by
  simp [sesq, Finset.sum_add_distrib, mul_add]

end SesquilinearSeed

section Basis

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v} [DecidableEq ι]

def basisVector (i : ι) : StateVector 𝕜 ι :=
  fun j => if j = i then 1 else 0

theorem basisVector_apply_same (i : ι) :
    basisVector (𝕜 := 𝕜) i i = 1 := by
  unfold basisVector
  exact if_pos rfl

theorem basisVector_apply_ne {i j : ι} (h : j ≠ i) :
    basisVector (𝕜 := 𝕜) i j = 0 := by
  unfold basisVector
  exact if_neg h

end Basis

end CNNA.PillarA.Foundation
