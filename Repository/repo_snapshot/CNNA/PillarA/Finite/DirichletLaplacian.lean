import CNNA.PillarA.Finite.Approximant
import CNNA.PillarA.Foundation.WeightPolicy
import CNNA.PillarA.Foundation.MatrixNorms

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

abbrev BoxLevel
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  Fin (T.cutoff + 1)

abbrev BoxVertex
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) :=
  Sigma fun L : BoxLevel Cell T => {x : Cell L.1 // x ∈ A.carrier L.1}

abbrev BoundaryVertex
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) :=
  Sigma fun L : BoxLevel Cell T => {x : Cell L.1 // x ∈ A.ports L.1}

abbrev InteriorVertex
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) :=
  Sigma fun L : BoxLevel Cell T => {x : Cell L.1 // x ∈ A.interiorCarrier L.1}

abbrev DirichletWeight
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (A : ApproximantStrong Cell T) :=
  BoxVertex (Cell := Cell) A → BoxVertex (Cell := Cell) A → ℝ

namespace BoxVertex

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell} {A : ApproximantStrong Cell T}

abbrev levelIndex (v : BoxVertex (Cell := Cell) A) : BoxLevel Cell T :=
  v.1

abbrev level (v : BoxVertex (Cell := Cell) A) : Nat :=
  v.1.1

abbrev cell (v : BoxVertex (Cell := Cell) A) : Cell v.1.1 :=
  v.2.1

theorem level_le_cutoff (v : BoxVertex (Cell := Cell) A) :
    v.level ≤ T.cutoff := by
  exact Nat.lt_succ_iff.mp v.1.2

theorem mem_carrier (v : BoxVertex (Cell := Cell) A) :
    v.cell ∈ A.carrier v.level := by
  exact v.2.2

theorem cell_mem_ports_or_interior (v : BoxVertex (Cell := Cell) A) :
    v.cell ∈ A.ports v.level ∨ v.cell ∈ A.interiorCarrier v.level := by
  have hx : v.cell ∈ A.carrier v.level := v.mem_carrier
  have hmem : v.cell ∈ A.interiorCarrier v.level ∪ A.ports v.level := by
    rw [A.carrier_union_interior_ports v.level]
    exact hx
  rcases Finset.mem_union.mp hmem with hInterior | hBoundary
  · exact Or.inr hInterior
  · exact Or.inl hBoundary

theorem not_mem_ports_and_interior (v : BoxVertex (Cell := Cell) A) :
    ¬ (v.cell ∈ A.ports v.level ∧ v.cell ∈ A.interiorCarrier v.level) := by
  intro h
  have hdisjoint := A.interior_boundary_disjoint v.level
  have hleft := Finset.disjoint_left.mp hdisjoint
  exact hleft h.2 h.1

end BoxVertex

namespace BoundaryVertex

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell} {A : ApproximantStrong Cell T}

abbrev levelIndex (v : BoundaryVertex (Cell := Cell) A) : BoxLevel Cell T :=
  v.1

abbrev level (v : BoundaryVertex (Cell := Cell) A) : Nat :=
  v.1.1

abbrev cell (v : BoundaryVertex (Cell := Cell) A) : Cell v.1.1 :=
  v.2.1

theorem level_le_cutoff (v : BoundaryVertex (Cell := Cell) A) :
    v.level ≤ T.cutoff := by
  exact Nat.lt_succ_iff.mp v.1.2

theorem mem_ports (v : BoundaryVertex (Cell := Cell) A) :
    v.cell ∈ A.ports v.level := by
  exact v.2.2

def toBoxVertex (v : BoundaryVertex (Cell := Cell) A) : BoxVertex (Cell := Cell) A :=
  ⟨v.1, ⟨v.2.1, A.ports_subset_carrier v.1.1 v.2.2⟩⟩

theorem toBoxVertex_level (v : BoundaryVertex (Cell := Cell) A) :
    v.toBoxVertex.level = v.level := by
  rfl

theorem toBoxVertex_cell (v : BoundaryVertex (Cell := Cell) A) :
    v.toBoxVertex.cell = v.cell := by
  rfl

end BoundaryVertex

namespace InteriorVertex

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell} {A : ApproximantStrong Cell T}

abbrev levelIndex (v : InteriorVertex (Cell := Cell) A) : BoxLevel Cell T :=
  v.1

abbrev level (v : InteriorVertex (Cell := Cell) A) : Nat :=
  v.1.1

abbrev cell (v : InteriorVertex (Cell := Cell) A) : Cell v.1.1 :=
  v.2.1

theorem level_le_cutoff (v : InteriorVertex (Cell := Cell) A) :
    v.level ≤ T.cutoff := by
  exact Nat.lt_succ_iff.mp v.1.2

theorem mem_interior (v : InteriorVertex (Cell := Cell) A) :
    v.cell ∈ A.interiorCarrier v.level := by
  exact v.2.2

def toBoxVertex (v : InteriorVertex (Cell := Cell) A) : BoxVertex (Cell := Cell) A :=
  ⟨v.1, ⟨v.2.1, A.interiorCarrier_subset_carrier v.1.1 v.2.2⟩⟩

theorem toBoxVertex_level (v : InteriorVertex (Cell := Cell) A) :
    v.toBoxVertex.level = v.level := by
  rfl

theorem toBoxVertex_cell (v : InteriorVertex (Cell := Cell) A) :
    v.toBoxVertex.cell = v.cell := by
  rfl

end InteriorVertex

namespace DirichletAnalytic

variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev Weight (V : Type u) :=
  V → V → ℝ

def degree (c : Weight V) (i : V) : ℝ :=
  ∑ j : V, if j = i then 0 else c i j

def offDiag (c : Weight V) (i j : V) : ℝ :=
  if j = i then 0 else c i j

def laplacian (c : Weight V) : Matrix V V ℝ :=
  fun i j => if i = j then degree c i else - offDiag c i j

def quadForm (Λ : Matrix V V ℝ) (f : V → ℝ) : ℝ :=
  ∑ i : V, f i * (Λ.mulVec f) i

def dirichletEnergy (c : Weight V) (f : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V, offDiag c i j * (f i - f j)^2

omit [Fintype V] in
theorem offDiag_self (c : Weight V) (i : V) :
    offDiag c i i = 0 := by
  simp [offDiag]

theorem degree_eq_sum_offDiag (c : Weight V) (i : V) :
    degree c i = ∑ j : V, offDiag c i j := by
  simp [degree, offDiag]

def AdmissibleOp (Λ : Matrix V V ℝ) : Prop :=
  Matrix.transpose Λ = Λ ∧
    (∀ i : V, (∑ j : V, Λ i j) = 0) ∧
    (∀ i j : V, i ≠ j → Λ i j ≤ 0)

theorem laplacian_symmetric_of_symm
    (c : Weight V)
    (hsymm : ∀ i j, c i j = c j i) :
    Matrix.transpose (laplacian c) = laplacian c := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [laplacian]
  · have hji : j ≠ i := by
      exact fun h => hij h.symm
    simp [Matrix.transpose, laplacian, offDiag, hij, hji, hsymm]

theorem laplacian_rowSum_zero (c : Weight V) (i : V) :
    (∑ j : V, laplacian c i j) = 0 := by
  have hsplit :
      ∑ x : V, offDiag c i x = Finset.sum (Finset.univ.erase i) (fun x : V => offDiag c i x) := by
    rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
    simp [offDiag]
  calc
    (∑ j : V, laplacian c i j)
        = degree c i + Finset.sum (Finset.univ.erase i) (fun j : V => -offDiag c i j) := by
            rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
            simp only [Finset.sdiff_singleton_eq_erase]
            congr 1
            · simp [laplacian]
            · apply Finset.sum_congr rfl
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [laplacian, show i ≠ j from fun h => hji h.symm]
    _ = degree c i - Finset.sum (Finset.univ.erase i) (fun j : V => offDiag c i j) := by
          rw [sub_eq_add_neg, Finset.sum_neg_distrib]
    _ = degree c i - ∑ j : V, offDiag c i j := by
          rw [← hsplit]
    _ = 0 := by
          rw [degree_eq_sum_offDiag]
          ring

def Sii (c : Weight V) (f : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V, offDiag c i j * (f i) ^ 2

def Sij (c : Weight V) (f : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V, offDiag c i j * (f i) * (f j)

def Sjj (c : Weight V) (f : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V, offDiag c i j * (f j) ^ 2

theorem Sii_eq_degree (c : Weight V) (f : V → ℝ) :
    Sii c f = ∑ i : V, (degree c i) * (f i) ^ 2 := by
  simp [Sii, degree, offDiag, mul_comm, Finset.mul_sum]

omit [Fintype V] in
theorem offDiag_symm_of_symm
    (c : Weight V) (hsymm : ∀ i j, c i j = c j i) (i j : V) :
    offDiag c i j = offDiag c j i := by
  by_cases h : j = i
  · subst h
    simp [offDiag]
  · have h' : i ≠ j := by
      exact fun hEq => h hEq.symm
    simp [offDiag, h, h', hsymm]

theorem Sjj_eq_degree_of_symm
    (c : Weight V) (hsymm : ∀ i j, c i j = c j i) (f : V → ℝ) :
    Sjj c f = ∑ j : V, (degree c j) * (f j) ^ 2 := by
  unfold Sjj
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  calc
    ∑ i : V, offDiag c i j * (f j) ^ 2 = (∑ i : V, offDiag c i j) * (f j) ^ 2 := by
      rw [Finset.sum_mul]
    _ = (∑ i : V, offDiag c j i) * (f j) ^ 2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa using offDiag_symm_of_symm c hsymm i j
    _ = (degree c j) * (f j) ^ 2 := by
      rw [degree_eq_sum_offDiag]

theorem dirichletEnergy_expand (c : Weight V) (f : V → ℝ) :
    dirichletEnergy c f = Sii c f - 2 * Sij c f + Sjj c f := by
  unfold dirichletEnergy
  have hterm :
      ∀ i j : V,
        offDiag c i j * (f i - f j) ^ 2 =
          offDiag c i j * (f i) ^ 2 - 2 * (offDiag c i j * f i * f j)
            + offDiag c i j * (f j) ^ 2 := by
    intro i j
    ring_nf
  have hSii :
      (∑ i : V, ∑ j : V, offDiag c i j * (f i) ^ 2) = Sii c f := by
    rfl
  have hSjj :
      (∑ i : V, ∑ j : V, offDiag c i j * (f j) ^ 2) = Sjj c f := by
    rfl
  have hTwoSij :
      (∑ i : V, ∑ j : V, 2 * (offDiag c i j * f i * f j)) = 2 * Sij c f := by
    unfold Sij
    calc
      ∑ i : V, ∑ j : V, 2 * (offDiag c i j * f i * f j)
          = ∑ i : V, 2 * (∑ j : V, offDiag c i j * f i * f j) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [← Finset.mul_sum]
      _ = 2 * ∑ i : V, ∑ j : V, offDiag c i j * f i * f j := by
            rw [← Finset.mul_sum]
      _ = 2 * Sij c f := by
            rfl
  calc
    ∑ i : V, ∑ j : V, offDiag c i j * (f i - f j) ^ 2
        = ∑ i : V, ∑ j : V,
            (offDiag c i j * (f i) ^ 2 - 2 * (offDiag c i j * f i * f j)
              + offDiag c i j * (f j) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            exact hterm i j
    _ = (∑ i : V, ∑ j : V, offDiag c i j * (f i) ^ 2)
          - (∑ i : V, ∑ j : V, 2 * (offDiag c i j * f i * f j))
          + (∑ i : V, ∑ j : V, offDiag c i j * (f j) ^ 2) := by
            simp [Finset.sum_add_distrib, sub_eq_add_neg]
    _ = Sii c f - (∑ i : V, ∑ j : V, 2 * (offDiag c i j * f i * f j)) + Sjj c f := by
          rw [hSii, hSjj]
    _ = Sii c f - 2 * Sij c f + Sjj c f := by
          rw [hTwoSij]

theorem quadForm_laplacian_eq_degree_sub_Sij (c : Weight V) (f : V → ℝ) :
    quadForm (laplacian c) f = (∑ i : V, (degree c i) * (f i) ^ 2) - Sij c f := by
  have hSij : ∑ i, f i * (∑ j, offDiag c i j * f j) = Sij c f := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  calc
    quadForm (laplacian c) f = ∑ i, f i * (∑ j, laplacian c i j * f j) := by
      rfl
    _ = ∑ i, f i * (degree c i * f i - ∑ j, offDiag c i j * f j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simp +decide [laplacian, degree, offDiag]
      simp +decide [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, sub_eq_add_neg]
      simp +decide [Finset.filter_ne']
    _ = (∑ i, degree c i * f i ^ 2) - ∑ i, f i * (∑ j, offDiag c i j * f j) := by
      simp [mul_sub, Finset.sum_sub_distrib, pow_two, mul_assoc, mul_comm]
    _ = (∑ i : V, (degree c i) * (f i) ^ 2) - Sij c f := by
      rw [hSij]

theorem dirichletEnergy_eq_two_mul_quadForm_of_symm
    (c : Weight V)
    (hsymm : ∀ i j, c i j = c j i)
    (f : V → ℝ) :
    dirichletEnergy c f = 2 * quadForm (laplacian c) f := by
  have hEnergy := dirichletEnergy_expand c f
  have hQuad := quadForm_laplacian_eq_degree_sub_Sij c f
  linarith [hEnergy, hQuad, Sii_eq_degree c f, Sjj_eq_degree_of_symm c hsymm f]

theorem quadForm_nonneg_of_symmetric_nonneg
    (c : Weight V)
    (hsymm : ∀ i j, c i j = c j i)
    (hnonneg : ∀ i j, 0 ≤ c i j)
    (f : V → ℝ) :
    0 ≤ quadForm (laplacian c) f := by
  have hoff : ∀ i j, 0 ≤ offDiag c i j := by
    intro i j
    by_cases h : j = i
    · subst h
      simp [offDiag]
    · simp [offDiag, h, hnonneg]
  have hterm : ∀ i j, 0 ≤ offDiag c i j * (f i - f j) ^ 2 := by
    intro i j
    exact mul_nonneg (hoff i j) (sq_nonneg (f i - f j))
  have hsum : 0 ≤ dirichletEnergy c f := by
    unfold dirichletEnergy
    refine Finset.sum_nonneg ?_
    intro i _
    refine Finset.sum_nonneg ?_
    intro j _
    exact hterm i j
  have hEq := dirichletEnergy_eq_two_mul_quadForm_of_symm c hsymm f
  have hq : 0 ≤ 2 * quadForm (laplacian c) f := by simpa [hEq] using hsum
  linarith

theorem laplacian_admissible
    (c : Weight V)
    (hsymm : ∀ i j, c i j = c j i)
    (hnonneg : ∀ i j, 0 ≤ c i j) :
    AdmissibleOp (laplacian c) := by
  constructor
  · exact laplacian_symmetric_of_symm c hsymm
  constructor
  · intro i
    exact laplacian_rowSum_zero c i
  · intro i j hij
    have h' : ¬ j = i := by
      exact fun hEq => hij hEq.symm
    simp [laplacian, offDiag, hij, h', hnonneg]

end DirichletAnalytic

structure DirichletLaplacianStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : ApproximantStrong Cell T
  policy : WeightPolicy

abbrev DirichletLaplacianStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  DirichletLaplacianStrong (Cell := Cell) T

abbrev DirichletLaplacianOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  DirichletLaplacianStrong (Cell := Cell) T

namespace DirichletLaplacianStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

def ofApproximant (A : ApproximantStrong Cell T) (P : WeightPolicy) :
    DirichletLaplacianStrong Cell T where
  source := A
  policy := P

def ofToC (X : ToCStrongOf Cell) (cp : ConcretePolicyOf) (wp : WeightPolicy) :
    DirichletLaplacianStrong Cell (X.approximant cp) :=
  ofApproximant (ToCStrong.fullApproximantVariant X cp) wp

def cast (h : T = U) (D : DirichletLaplacianStrong Cell T) :
    DirichletLaplacianStrong Cell U := by
  cases h
  exact D

theorem cast_rfl (D : DirichletLaplacianStrong Cell T) :
    cast (Cell := Cell) rfl D = D := by
  rfl

abbrev boxVertex (D : DirichletLaplacianStrong Cell T) :=
  BoxVertex (Cell := Cell) D.source

abbrev boundaryVertex (D : DirichletLaplacianStrong Cell T) :=
  BoundaryVertex (Cell := Cell) D.source

abbrev interiorVertex (D : DirichletLaplacianStrong Cell T) :=
  InteriorVertex (Cell := Cell) D.source

def weight (D : DirichletLaplacianStrong Cell T) :
    DirichletWeight (Cell := Cell) D.source :=
  fun i j => D.policy.constantWeight i j

theorem weight_symm (D : DirichletLaplacianStrong Cell T) (i j : D.boxVertex) :
    D.weight i j = D.weight j i := by
  exact D.policy.constantWeight_symm i j

theorem weight_nonneg (D : DirichletLaplacianStrong Cell T) (i j : D.boxVertex) :
    0 ≤ D.weight i j := by
  exact D.policy.constantWeight_nonneg i j

def matrix (D : DirichletLaplacianStrong Cell T) :
    Matrix D.boxVertex D.boxVertex ℝ :=
  DirichletAnalytic.laplacian D.weight

def degree (D : DirichletLaplacianStrong Cell T) (i : D.boxVertex) : ℝ :=
  DirichletAnalytic.degree D.weight i

def offDiag (D : DirichletLaplacianStrong Cell T) (i j : D.boxVertex) : ℝ :=
  DirichletAnalytic.offDiag D.weight i j

def quadForm (D : DirichletLaplacianStrong Cell T) (f : D.boxVertex → ℝ) : ℝ :=
  DirichletAnalytic.quadForm D.matrix f

def dirichletEnergy (D : DirichletLaplacianStrong Cell T) (f : D.boxVertex → ℝ) : ℝ :=
  DirichletAnalytic.dirichletEnergy D.weight f

def admissible (D : DirichletLaplacianStrong Cell T) : Prop :=
  DirichletAnalytic.AdmissibleOp D.matrix

theorem matrix_symmetric (D : DirichletLaplacianStrong Cell T) :
    Matrix.transpose D.matrix = D.matrix := by
  exact DirichletAnalytic.laplacian_symmetric_of_symm D.weight (D.weight_symm)

theorem rowSum_zero (D : DirichletLaplacianStrong Cell T) (i : D.boxVertex) :
    (∑ j : D.boxVertex, D.matrix i j) = 0 := by
  exact DirichletAnalytic.laplacian_rowSum_zero D.weight i

theorem quadForm_nonneg (D : DirichletLaplacianStrong Cell T)
    (f : D.boxVertex → ℝ) :
    0 ≤ D.quadForm f := by
  exact DirichletAnalytic.quadForm_nonneg_of_symmetric_nonneg
    D.weight (D.weight_symm) (D.weight_nonneg) f

theorem admissible_matrix (D : DirichletLaplacianStrong Cell T) :
    D.admissible := by
  exact DirichletAnalytic.laplacian_admissible D.weight (D.weight_symm) (D.weight_nonneg)

def boundaryBlock (D : DirichletLaplacianStrong Cell T) :
    Matrix D.boundaryVertex D.boundaryVertex ℝ :=
  fun i j => D.matrix (BoundaryVertex.toBoxVertex i) (BoundaryVertex.toBoxVertex j)

def boundaryInteriorBlock (D : DirichletLaplacianStrong Cell T) :
    Matrix D.boundaryVertex D.interiorVertex ℝ :=
  fun i j => D.matrix (BoundaryVertex.toBoxVertex i) (InteriorVertex.toBoxVertex j)

def interiorBoundaryBlock (D : DirichletLaplacianStrong Cell T) :
    Matrix D.interiorVertex D.boundaryVertex ℝ :=
  fun i j => D.matrix (InteriorVertex.toBoxVertex i) (BoundaryVertex.toBoxVertex j)

def interiorBlock (D : DirichletLaplacianStrong Cell T) :
    Matrix D.interiorVertex D.interiorVertex ℝ :=
  fun i j => D.matrix (InteriorVertex.toBoxVertex i) (InteriorVertex.toBoxVertex j)

theorem boundaryBlock_transpose (D : DirichletLaplacianStrong Cell T) :
    Matrix.transpose D.boundaryBlock = D.boundaryBlock := by
  ext i j
  have h := congrArg
    (fun M => M (BoundaryVertex.toBoxVertex i) (BoundaryVertex.toBoxVertex j))
    D.matrix_symmetric
  simpa [boundaryBlock, Matrix.transpose] using h

theorem interiorBlock_transpose (D : DirichletLaplacianStrong Cell T) :
    Matrix.transpose D.interiorBlock = D.interiorBlock := by
  ext i j
  have h := congrArg
    (fun M => M (InteriorVertex.toBoxVertex i) (InteriorVertex.toBoxVertex j))
    D.matrix_symmetric
  simpa [interiorBlock, Matrix.transpose] using h

theorem interiorBoundaryBlock_transpose (D : DirichletLaplacianStrong Cell T) :
    Matrix.transpose D.boundaryInteriorBlock = D.interiorBoundaryBlock := by
  ext i j
  have h := congrArg
    (fun M => M (InteriorVertex.toBoxVertex i) (BoundaryVertex.toBoxVertex j))
    D.matrix_symmetric
  simpa [boundaryInteriorBlock, interiorBoundaryBlock, Matrix.transpose] using h

theorem boundaryInteriorBlock_transpose (D : DirichletLaplacianStrong Cell T) :
    Matrix.transpose D.interiorBoundaryBlock = D.boundaryInteriorBlock := by
  ext i j
  have h := congrArg
    (fun M => M (BoundaryVertex.toBoxVertex i) (InteriorVertex.toBoxVertex j))
    D.matrix_symmetric
  simpa [boundaryInteriorBlock, interiorBoundaryBlock, Matrix.transpose] using h

def frobSq (D : DirichletLaplacianStrong Cell T) : ℝ :=
  CNNA.PillarA.Foundation.MatrixNorm.Analytic.frobSq D.matrix

theorem frobSq_nonneg (D : DirichletLaplacianStrong Cell T) :
    0 ≤ D.frobSq := by
  exact CNNA.PillarA.Foundation.MatrixNorm.Analytic.frobSq_nonneg D.matrix

end DirichletLaplacianStrong

namespace StrengtheningS5

open CNNA.PillarA.Finite.StrengtheningS4


def referenceDefaultWeightPolicy (b : Nat) : WeightPolicy :=
  WeightPolicy.reference (b + 1) (by
    have h : 0 < b + 1 := Nat.succ_pos b
    exact_mod_cast h)

def referenceFullDirichletLaplacian (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    DirichletLaplacianStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  DirichletLaplacianStrong.ofApproximant (referenceFullApproximant b p) wp

def variationFullDirichletLaplacian (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    DirichletLaplacianStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  DirichletLaplacianStrong.ofApproximant (variationFullApproximant β p) wp

end StrengtheningS5

end CNNA.PillarA.Finite
