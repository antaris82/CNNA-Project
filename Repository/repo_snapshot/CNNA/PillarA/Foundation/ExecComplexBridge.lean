import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import CNNA.PillarA.Foundation.MatrixAlgebra
import CNNA.PillarA.Foundation.MatrixNorms

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Foundation
namespace ExecComplexBridge

universe u v w

def toComplex (z : ExecComplex) : ℂ :=
  { re := z.re, im := z.im }

theorem toComplex_re (z : ExecComplex) : (toComplex z).re = z.re := by
  rfl

theorem toComplex_im (z : ExecComplex) : (toComplex z).im = z.im := by
  rfl

theorem toComplex_zero : toComplex 0 = 0 := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.zero_re]
  · simp [toComplex, ExecComplex.zero_im]

theorem toComplex_one : toComplex 1 = 1 := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.one_re]
  · simp [toComplex, ExecComplex.one_im]

theorem toComplex_add (z w : ExecComplex) :
    toComplex (z + w) = toComplex z + toComplex w := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.add_re]
  · simp [toComplex, ExecComplex.add_im]

theorem toComplex_neg (z : ExecComplex) :
    toComplex (-z) = -toComplex z := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.neg_re]
  · simp [toComplex, ExecComplex.neg_im]

theorem toComplex_sub (z w : ExecComplex) :
    toComplex (z - w) = toComplex z - toComplex w := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.sub_re]
  · simp [toComplex, ExecComplex.sub_im]

theorem toComplex_mul (z w : ExecComplex) :
    toComplex (z * w) = toComplex z * toComplex w := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.mul_re, Complex.mul_re]
  · simp [toComplex, ExecComplex.mul_im, Complex.mul_im]

theorem toComplex_star (z : ExecComplex) :
    toComplex (star z) = star (toComplex z) := by
  apply Complex.ext
  · simp [toComplex, ExecComplex.star_def]
  · simp [toComplex, ExecComplex.star_def]

theorem toComplex_ofRat (q : ℚ) :
    toComplex (ExecComplex.ofRat q) = (q : ℂ) := by
  apply Complex.ext <;> simp [toComplex, ExecComplex.ofRat]



theorem toComplex_sum {α : Type u} [DecidableEq α] (s : Finset α) (f : α → ExecComplex) :
    toComplex (s.sum f) = s.sum (fun a => toComplex (f a)) := by
  refine Finset.induction_on s ?_ ?_
  · simp [toComplex_zero]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs, toComplex_add]

theorem toComplex_injective : Function.Injective toComplex := by
  intro z w h
  apply ExecComplex.ext
  · have hre : ((z.re : ℝ) = (w.re : ℝ)) := by
      simpa [toComplex] using congrArg Complex.re h
    exact_mod_cast hre
  · have him : ((z.im : ℝ) = (w.im : ℝ)) := by
      simpa [toComplex] using congrArg Complex.im h
    exact_mod_cast him

def toComplexHom : ExecComplex →+* ℂ where
  toFun := toComplex
  map_zero' := toComplex_zero
  map_one' := toComplex_one
  map_add' := toComplex_add
  map_mul' := toComplex_mul

theorem toComplexHom_apply (z : ExecComplex) : toComplexHom z = toComplex z := by
  rfl

theorem toComplexHom_injective : Function.Injective toComplexHom :=
  toComplex_injective

instance instSeedScalarComplex : SeedScalar ℂ where
  toCommRing := inferInstance
  toStarRing := inferInstance

def mapVector {ι : Type v} (v : StateVector ExecComplex ι) : StateVector ℂ ι :=
  fun i => toComplex (v i)

def mapMatrix {m : Type v} {n : Type w} (A : Matrix m n ExecComplex) : Matrix m n ℂ :=
  A.map toComplex

theorem mapVector_apply {ι : Type v} (v : StateVector ExecComplex ι) (i : ι) :
    mapVector v i = toComplex (v i) := by
  rfl

theorem mapMatrix_apply {m : Type v} {n : Type w} (A : Matrix m n ExecComplex) (i : m) (j : n) :
    mapMatrix A i j = toComplex (A i j) := by
  rfl

theorem mapVector_injective {ι : Type v} : Function.Injective (@mapVector ι) := by
  intro v w h
  funext i
  exact toComplex_injective (by simpa [mapVector] using congrArg (fun x => x i) h)

theorem mapMatrix_injective {m : Type v} {n : Type w} : Function.Injective (@mapMatrix m n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  exact toComplex_injective (by simpa [mapMatrix] using congrArg (fun M => M i j) h)

def mapSquareMatrix {ι : Type v} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ExecComplex →+* Matrix ι ι ℂ :=
  toComplexHom.mapMatrix

theorem mapSquareMatrix_apply {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ExecComplex) :
    mapSquareMatrix A = mapMatrix A := by
  ext i j
  simp [mapSquareMatrix, mapMatrix, toComplexHom_apply]

theorem mapMatrix_add {m : Type v} {n : Type w}
    (A B : Matrix m n ExecComplex) :
    mapMatrix (A + B) = mapMatrix A + mapMatrix B := by
  ext i j
  simp [mapMatrix, toComplex_add]

theorem mapMatrix_sub {m : Type v} {n : Type w}
    (A B : Matrix m n ExecComplex) :
    mapMatrix (A - B) = mapMatrix A - mapMatrix B := by
  ext i j
  simp [mapMatrix, toComplex_sub]

theorem mapMatrix_conjTranspose {m : Type v} {n : Type w}
    (A : Matrix m n ExecComplex) :
    mapMatrix (A.conjTranspose) = (mapMatrix A).conjTranspose := by
  ext i j
  simp [mapMatrix, toComplex_star]

theorem mapMatrix_mul {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ExecComplex) :
    mapMatrix (A * B) = mapMatrix A * mapMatrix B := by
  rw [← mapSquareMatrix_apply (A := A * B), ← mapSquareMatrix_apply (A := A), ← mapSquareMatrix_apply (A := B)]
  exact (mapSquareMatrix (ι := ι)).map_mul A B

theorem map_act {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Observable ExecComplex ι) (v : StateVector ExecComplex ι) :
    mapVector (act A v) = act (𝕜 := ℂ) (mapMatrix A) (mapVector v) := by
  funext i
  rw [act_apply]
  change toComplex (∑ j : ι, A i j * v j) = ∑ j : ι, toComplex (A i j) * toComplex (v j)
  rw [toComplex_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [toComplex_mul]

theorem map_sesq {ι : Type v} [Fintype ι] [DecidableEq ι]
    (v w : StateVector ExecComplex ι) :
    toComplex (sesq (𝕜 := ExecComplex) v w) = sesq (𝕜 := ℂ) (mapVector v) (mapVector w) := by
  rw [sesq_def, sesq_def]
  change toComplex (∑ i : ι, star (v i) * w i) =
      ∑ i : ι, star (toComplex (v i)) * toComplex (w i)
  rw [toComplex_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [toComplex_mul, toComplex_star]

theorem map_adjoint {ι : Type v}
    (A : Observable ExecComplex ι) :
    mapMatrix (adjoint A) = adjoint (𝕜 := ℂ) (mapMatrix A) := by
  ext i j
  simp [adjoint, mapMatrix, toComplex_star]

theorem map_commutator {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A B : Observable ExecComplex ι) :
    mapMatrix (commutator (𝕜 := ExecComplex) A B) =
      commutator (𝕜 := ℂ) (mapMatrix A) (mapMatrix B) := by
  simp [commutator, mapMatrix_sub, mapMatrix_mul]

theorem map_anticommutator {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A B : Observable ExecComplex ι) :
    mapMatrix (anticommutator (𝕜 := ExecComplex) A B) =
      anticommutator (𝕜 := ℂ) (mapMatrix A) (mapMatrix B) := by
  simp [anticommutator, mapMatrix_add, mapMatrix_mul]

theorem map_isHermitian {ι : Type v} [Fintype ι] [DecidableEq ι]
    {A : Observable ExecComplex ι} (hA : IsHermitian A) :
    IsHermitian (mapMatrix A) := by
  rw [isHermitian_iff] at hA ⊢
  simpa [mapMatrix_conjTranspose] using congrArg mapMatrix hA

def mapHermitian {ι : Type v} [Fintype ι] [DecidableEq ι]
    (H : HermitianMatrix (𝕜 := ExecComplex) (ι := ι)) :
    HermitianMatrix (𝕜 := ℂ) (ι := ι) where
  matrix := mapMatrix H.matrix
  hermitian := map_isHermitian H.hermitian

namespace Mirror

section Frob

variable {ι : Type u} [Fintype ι]

def frobSq (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i : ι, ∑ j : ι, Complex.normSq (A i j)

def deltaRegularization (ε : ℚ) (A : Matrix ι ι ℂ) : ℝ :=
  (ε : ℝ) * max (1 : ℝ) (frobSq A)

theorem frobSq_nonneg (A : Matrix ι ι ℂ) : 0 ≤ frobSq A := by
  unfold frobSq
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  exact Complex.normSq_nonneg _

theorem sqNorm_map (z : ExecComplex) :
    Complex.normSq (toComplex z) = (MatrixNorm.Exec.sqNorm z : ℝ) := by
  change ((z.re : ℝ) * (z.re : ℝ) + (z.im : ℝ) * (z.im : ℝ)) =
      (((z.re ^ 2 + z.im ^ 2 : ℚ) : ℝ))
  simp [pow_two]

theorem frobSq_mapMatrix [DecidableEq ι] (A : Matrix ι ι ExecComplex) :
    frobSq (mapMatrix A) = (MatrixNorm.Exec.frobSq A : ℝ) := by
  unfold frobSq MatrixNorm.Exec.frobSq mapMatrix
  simp [sqNorm_map]

theorem frobeniusSq_mapExecMat [DecidableEq ι] (A : MatrixNorm.Exec.ExecMat ι) :
    frobSq (mapMatrix A) = (MatrixNorm.Exec.frobeniusSq A : ℝ) := by
  simpa [MatrixNorm.Exec.frobeniusSq_eq_frobSq] using frobSq_mapMatrix (A := A)

theorem deltaRegularization_mapMatrix [DecidableEq ι]
    (ε : ℚ) (A : Matrix ι ι ExecComplex) :
    deltaRegularization ε (mapMatrix A) =
      (MatrixNorm.Exec.deltaRegularization ε A : ℝ) := by
  unfold deltaRegularization MatrixNorm.Exec.deltaRegularization
  rw [frobSq_mapMatrix]
  simp

theorem shift_mapExecMat [DecidableEq ι] (ε : ℚ) (A : MatrixNorm.Exec.ExecMat ι) :
    deltaRegularization ε (mapMatrix A) = (MatrixNorm.Exec.shift ε A : ℝ) := by
  simpa [MatrixNorm.Exec.shift_eq_deltaRegularization] using
    deltaRegularization_mapMatrix (ε := ε) (A := A)

end Frob

end Mirror

end ExecComplexBridge
end CNNA.PillarA.Foundation
