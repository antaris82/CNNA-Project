import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import CNNA.PillarA.Foundation.FiniteHilbert

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Foundation

universe u v

abbrev Observable (𝕜 : Type u) (ι : Type v) : Type (max u v) :=
  Matrix ι ι 𝕜

section MatrixAdjoint

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v}

def adjoint (A : Observable 𝕜 ι) : Observable 𝕜 ι :=
  A.conjTranspose

theorem adjoint_eq_conjTranspose (A : Observable 𝕜 ι) :
    adjoint A = A.conjTranspose := by
  rfl

end MatrixAdjoint

section MatrixSeed

variable {𝕜 : Type u} [SeedScalar 𝕜]
variable {ι : Type v} [Fintype ι]

def act (A : Observable 𝕜 ι) (v : StateVector 𝕜 ι) : StateVector 𝕜 ι :=
  fun i => ∑ j : ι, A i j * v j

def commutator (A B : Observable 𝕜 ι) : Observable 𝕜 ι :=
  A * B - B * A

def anticommutator (A B : Observable 𝕜 ι) : Observable 𝕜 ι :=
  A * B + B * A

theorem act_apply (A : Observable 𝕜 ι) (v : StateVector 𝕜 ι) (i : ι) :
    act A v i = ∑ j : ι, A i j * v j := by
  rfl

theorem commutator_eq (A B : Observable 𝕜 ι) :
    commutator A B = A * B - B * A := by
  rfl

theorem anticommutator_eq (A B : Observable 𝕜 ι) :
    anticommutator A B = A * B + B * A := by
  rfl

theorem commutator_self (A : Observable 𝕜 ι) :
    commutator A A = 0 := by
  simp [commutator]

theorem anticommutator_self (A : Observable 𝕜 ι) :
    anticommutator A A = A * A + A * A := by
  rfl

end MatrixSeed

end CNNA.PillarA.Foundation
