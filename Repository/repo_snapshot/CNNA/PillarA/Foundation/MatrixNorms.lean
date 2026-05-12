import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import CNNA.PillarA.Foundation.ExecComplex

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Foundation
namespace MatrixNorm

universe u

namespace Exec

open ExecComplex

section Frob

variable {ι : Type u} [Fintype ι]

def sqNorm (z : ExecComplex) : ℚ :=
  z.re ^ 2 + z.im ^ 2

theorem sqNorm_nonneg (z : ExecComplex) : 0 ≤ sqNorm z := by
  unfold sqNorm
  exact add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)

theorem sqNorm_eq_zero_iff (z : ExecComplex) : sqNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hre_nonneg : 0 ≤ z.re ^ 2 := sq_nonneg z.re
    have him_nonneg : 0 ≤ z.im ^ 2 := sq_nonneg z.im
    have hre_le_zero : z.re ^ 2 ≤ 0 := by
      calc
        z.re ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by
          exact le_add_of_nonneg_right him_nonneg
        _ = 0 := h
    have him_le_zero : z.im ^ 2 ≤ 0 := by
      calc
        z.im ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by
          exact le_add_of_nonneg_left hre_nonneg
        _ = 0 := h
    have hre_zero_sq : z.re ^ 2 = 0 := le_antisymm hre_le_zero hre_nonneg
    have him_zero_sq : z.im ^ 2 = 0 := le_antisymm him_le_zero him_nonneg
    have hre_zero : z.re = 0 := by
      exact eq_zero_of_pow_eq_zero hre_zero_sq
    have him_zero : z.im = 0 := by
      exact eq_zero_of_pow_eq_zero him_zero_sq
    ext
    · exact hre_zero
    · exact him_zero
  · rintro rfl
    simp [sqNorm, ExecComplex.zero_re, ExecComplex.zero_im]

theorem sqNorm_pos_of_ne_zero (z : ExecComplex) (hz : z ≠ 0) :
    0 < sqNorm z := by
  have h0 : sqNorm z ≠ 0 := by
    intro h
    exact hz ((sqNorm_eq_zero_iff z).1 h)
  exact lt_of_le_of_ne (sqNorm_nonneg z) (Ne.symm h0)

theorem sqNorm_star (z : ExecComplex) : sqNorm (star z) = sqNorm z := by
  unfold sqNorm
  simp [ExecComplex.star_def]

def frobSq (A : Matrix ι ι ExecComplex) : ℚ :=
  ∑ i : ι, ∑ j : ι, sqNorm (A i j)

def isZero [DecidableEq ι] (A : Matrix ι ι ExecComplex) : Bool :=
  decide (A = 0)

theorem isZero_eq_true_iff [DecidableEq ι] (A : Matrix ι ι ExecComplex) :
    isZero A = true ↔ A = 0 := by
  unfold isZero
  exact decide_eq_true_iff

theorem frobSq_nonneg (A : Matrix ι ι ExecComplex) : 0 ≤ frobSq A := by
  unfold frobSq
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  exact sqNorm_nonneg (A i j)

theorem frobSq_eq_zero_iff [DecidableEq ι] (A : Matrix ι ι ExecComplex) :
    frobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    have hOuter :
        ∀ i' ∈ (Finset.univ : Finset ι),
          (∑ j' : ι, sqNorm (A i' j')) = 0 := by
      have hNonneg :
          ∀ i' ∈ (Finset.univ : Finset ι), 0 ≤ (∑ j' : ι, sqNorm (A i' j')) := by
        intro i' _
        exact Finset.sum_nonneg (by
          intro j' _
          exact sqNorm_nonneg (A i' j'))
      have hSumZero := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).1 (by
        simpa [frobSq] using h)
      intro i' hi'
      exact hSumZero i' hi'
    have hInner :
        ∀ j' ∈ (Finset.univ : Finset ι), sqNorm (A i j') = 0 := by
      have hNonneg :
          ∀ j' ∈ (Finset.univ : Finset ι), 0 ≤ sqNorm (A i j') := by
        intro j' _
        exact sqNorm_nonneg (A i j')
      have hSumZero := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).1 (by
        simpa using hOuter i (by simp))
      intro j' hj'
      exact hSumZero j' hj'
    exact (sqNorm_eq_zero_iff (A i j)).1 (hInner j (by simp))
  · rintro rfl
    simp [frobSq, sqNorm, ExecComplex.zero_re, ExecComplex.zero_im]

theorem frobSq_pos_of_ne_zero [DecidableEq ι] (A : Matrix ι ι ExecComplex) (hA : A ≠ 0) :
    0 < frobSq A := by
  have h0 : frobSq A ≠ 0 := by
    intro h
    exact hA ((frobSq_eq_zero_iff A).1 h)
  exact lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm h0)

def deltaRegularization (ε : ℚ) (A : Matrix ι ι ExecComplex) : ℚ :=
  ε * max (1 : ℚ) (frobSq A)

abbrev ExecMat (ι : Type u) : Type u :=
  Matrix ι ι ExecComplex

def frobeniusSq (A : ExecMat ι) : ℚ :=
  frobSq A

def zeroTest [DecidableEq ι] (A : ExecMat ι) : Bool :=
  isZero A

def shift (ε : ℚ) (A : ExecMat ι) : ℚ :=
  deltaRegularization ε A

theorem frobeniusSq_eq_frobSq (A : ExecMat ι) :
    frobeniusSq A = frobSq A := by
  rfl

theorem zeroTest_eq_isZero [DecidableEq ι] (A : ExecMat ι) :
    zeroTest A = isZero A := by
  rfl

theorem shift_eq_deltaRegularization (ε : ℚ) (A : ExecMat ι) :
    shift ε A = deltaRegularization ε A := by
  rfl

theorem frobeniusSq_nonneg (A : ExecMat ι) : 0 ≤ frobeniusSq A := by
  exact frobSq_nonneg A

theorem zeroTest_eq_true_iff [DecidableEq ι] (A : ExecMat ι) :
    zeroTest A = true ↔ A = 0 := by
  exact isZero_eq_true_iff A

theorem frobeniusSq_eq_zero_iff [DecidableEq ι] (A : ExecMat ι) :
    frobeniusSq A = 0 ↔ A = 0 := by
  exact frobSq_eq_zero_iff A

theorem frobeniusSq_pos_of_ne_zero [DecidableEq ι] (A : ExecMat ι) (hA : A ≠ 0) :
    0 < frobeniusSq A := by
  exact frobSq_pos_of_ne_zero A hA

theorem shift_pos (ε : ℚ) (hε : 0 < ε) (A : ExecMat ι) :
    0 < shift ε A := by
  have hmax : 0 < max (1 : ℚ) (frobSq A) := by
    have h1 : (0 : ℚ) < 1 := by
      exact zero_lt_one
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  simpa [shift, deltaRegularization] using mul_pos hε hmax

theorem shift_ge_epsilon (ε : ℚ) (hε : 0 ≤ ε) (A : ExecMat ι) :
    ε ≤ shift ε A := by
  have hmax : (1 : ℚ) ≤ max (1 : ℚ) (frobSq A) := by
    exact le_max_left _ _
  have hmul : ε * 1 ≤ ε * max (1 : ℚ) (frobSq A) := by
    exact mul_le_mul_of_nonneg_left hmax hε
  simpa [shift, deltaRegularization, mul_one] using hmul

theorem deltaRegularization_pos (ε : ℚ) (hε : 0 < ε) (A : Matrix ι ι ExecComplex) :
    0 < deltaRegularization ε A := by
  have hmax : 0 < max (1 : ℚ) (frobSq A) := by
    have h1 : (0 : ℚ) < 1 := by exact zero_lt_one
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  simpa [deltaRegularization] using mul_pos hε hmax

theorem deltaRegularization_ge_epsilon (ε : ℚ) (hε : 0 ≤ ε) (A : Matrix ι ι ExecComplex) :
    ε ≤ deltaRegularization ε A := by
  have hmax : (1 : ℚ) ≤ max (1 : ℚ) (frobSq A) := by
    exact le_max_left _ _
  have hmul : ε * 1 ≤ ε * max (1 : ℚ) (frobSq A) := by
    exact mul_le_mul_of_nonneg_left hmax hε
  simpa [deltaRegularization, mul_one] using hmul

end Frob

end Exec

namespace Analytic

section RealFrob

variable {ι : Type u} [Fintype ι]

def frobSq (A : Matrix ι ι ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, (A i j) ^ 2

section Rectangular

variable {κ : Type u} [Fintype κ]

def frobSqRect (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i : ι, ∑ j : κ, (A i j) ^ 2

theorem frobSqRect_eq_frobSq (A : Matrix ι ι ℝ) :
    frobSqRect A = frobSq A := by
  rfl

theorem frobSqRect_nonneg (A : Matrix ι κ ℝ) : 0 ≤ frobSqRect A := by
  unfold frobSqRect
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  exact sq_nonneg (A i j)

theorem frobSqRect_zero :
    frobSqRect (0 : Matrix ι κ ℝ) = 0 := by
  unfold frobSqRect
  simp

end Rectangular

def deltaRegularization (ε : ℝ) (A : Matrix ι ι ℝ) : ℝ :=
  ε * max (1 : ℝ) (frobSq A)

theorem frobSq_nonneg (A : Matrix ι ι ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  exact sq_nonneg (A i j)

theorem deltaRegularization_pos (ε : ℝ) (hε : 0 < ε) (A : Matrix ι ι ℝ) :
    0 < deltaRegularization ε A := by
  have hmax : 0 < max (1 : ℝ) (frobSq A) := by
    have h1 : (0 : ℝ) < 1 := by
      exact zero_lt_one
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  simpa [deltaRegularization] using mul_pos hε hmax

theorem frobSq_eq_zero_iff [DecidableEq ι] (A : Matrix ι ι ℝ) : frobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hOuter :
        ∀ i' ∈ (Finset.univ : Finset ι),
          (∑ j' : ι, (A i' j') ^ 2) = 0 := by
      have hNonneg :
          ∀ i' ∈ (Finset.univ : Finset ι), 0 ≤ (∑ j' : ι, (A i' j') ^ 2) := by
        intro i' _
        exact Finset.sum_nonneg (by
          intro j' _
          exact sq_nonneg (A i' j'))
      have hSumZero := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).1 (by
        simpa [frobSq] using h)
      intro i' hi'
      exact hSumZero i' hi'
    have hInner :
        ∀ j' ∈ (Finset.univ : Finset ι), (A i j') ^ 2 = 0 := by
      have hNonneg :
          ∀ j' ∈ (Finset.univ : Finset ι), 0 ≤ (A i j') ^ 2 := by
        intro j' _
        exact sq_nonneg (A i j')
      have hSumZero := (Finset.sum_eq_zero_iff_of_nonneg hNonneg).1 (by
        simpa using hOuter i (by simp))
      intro j' hj'
      exact hSumZero j' hj'
    have hPow : (A i j) ^ 2 = 0 :=
      hInner j (by simp)
    have hMul : A i j * A i j = 0 := by
      simpa [pow_two] using hPow
    rcases mul_eq_zero.mp hMul with hzero | hzero
    · exact hzero
    · exact hzero
  · intro h
    simp [frobSq, h]

theorem frobSq_pos_of_ne_zero [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A ≠ 0) :
    0 < frobSq A := by
  have h0 : frobSq A ≠ 0 := by
    intro h
    exact hA ((frobSq_eq_zero_iff A).1 h)
  exact lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm h0)

end RealFrob


end Analytic

end MatrixNorm
end CNNA.PillarA.Foundation
