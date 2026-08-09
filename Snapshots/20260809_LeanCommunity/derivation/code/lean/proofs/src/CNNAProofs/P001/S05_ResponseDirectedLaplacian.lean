import CNNAProofs.P001.S04_ResponseWellDefinedness

/-!
# P001 — S08 directed response/Laplacian structure

This module proves the directed Laplace/Z-matrix structure of every exact C006
response representative after S07 response well-definedness.

For one boundary basis vector `e_q`, the associated full potential is assembled
explicitly from the C006 solve convention `X` and the harmonic convention
`H = -X`.  The generic directed maximum principle yields the interval bound
`0 ≤ H(e_q) ≤ 1`.  The response entry is then identified with the full
Laplacian action at the corresponding boundary row.

The proof has four outputs:

1. off-diagonal response entries are nonpositive;
2. every response row sums to zero;
3. every diagonal response entry is nonnegative;
4. every exact response representative satisfies `IsDirectedLaplacianResponse`.

Strict distinguished-port positivity is intentionally excluded and remains S09.
No inverse, determinant, regularizer, pseudoinverse, symmetrization, selected
solver, or grounding vertex is introduced.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- Rational boundary basis vector with value one at `column`. -/
def boundaryBasis {boundary : Nat}
    (column row : Fin boundary) : ℚ :=
  if row = column then 1 else 0

/-- The boundary basis is pointwise nonnegative. -/
theorem boundaryBasis_nonnegative {boundary : Nat}
    (column row : Fin boundary) :
    0 ≤ boundaryBasis column row := by
  by_cases hRow : row = column
  · rw [boundaryBasis, if_pos hRow]
    exact zero_le_one
  · rw [boundaryBasis, if_neg hRow]

/-- The boundary basis is pointwise at most one. -/
theorem boundaryBasis_le_one {boundary : Nat}
    (column row : Fin boundary) :
    boundaryBasis column row ≤ 1 := by
  by_cases hRow : row = column
  · rw [boundaryBasis, if_pos hRow]
  · rw [boundaryBasis, if_neg hRow]
    exact zero_le_one

/-- Full harmonic potential associated with one boundary basis column.  C006
    stores `X`, while the physical harmonic extension is `H = -X`. -/
def harmonicBasisPotential {boundary interior : Nat}
    (solve : RationalMatrix interior boundary)
    (column : Fin boundary) : CutPotential boundary interior :=
  fun vertex =>
    match vertex with
    | Sum.inl row => boundaryBasis column row
    | Sum.inr row => -solve row column

/-- One matrix solve equation exposed at a single row and boundary column. -/
theorem interiorSolve_columnEquation {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve)
    (row : Fin interior)
    (column : Fin boundary) :
    (∑ middle, blocks.kII row middle * solve middle column) =
      blocks.kIB row column := by
  have hEntry := congrFun (congrFun hSolve row) column
  change
    (∑ middle, blocks.kII row middle * solve middle column) =
      blocks.kIB row column at hEntry
  exact hEntry

/-- Every basis potential is harmonic at every interior coordinate. -/
theorem harmonicBasisPotential_isInteriorHarmonic {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve)
    (column : Fin boundary) :
    IsInteriorHarmonic blocks (harmonicBasisPotential solve column) := by
  intro row
  unfold laplacianAction
  rw [Fintype.sum_sum_type]
  change
    (∑ boundaryIndex,
        blocks.kIB row boundaryIndex * boundaryBasis column boundaryIndex) +
      (∑ middle, blocks.kII row middle * (-solve middle column)) = 0
  have hBoundaryTerm :
      (∑ boundaryIndex,
        blocks.kIB row boundaryIndex * boundaryBasis column boundaryIndex) =
        blocks.kIB row column := by
    calc
      (∑ boundaryIndex,
          blocks.kIB row boundaryIndex * boundaryBasis column boundaryIndex) =
          ∑ boundaryIndex,
            if boundaryIndex = column then blocks.kIB row boundaryIndex else 0 := by
        apply Finset.sum_congr rfl
        intro boundaryIndex _hBoundaryIndex
        by_cases hIndex : boundaryIndex = column
        · rw [boundaryBasis, if_pos hIndex, if_pos hIndex, mul_one]
        · rw [boundaryBasis, if_neg hIndex, if_neg hIndex, mul_zero]
      _ = blocks.kIB row column := by
        exact Fintype.sum_ite_eq' column (fun boundaryIndex => blocks.kIB row boundaryIndex)
  have hInteriorTerm :
      (∑ middle, blocks.kII row middle * (-solve middle column)) =
        -(∑ middle, blocks.kII row middle * solve middle column) := by
    calc
      (∑ middle, blocks.kII row middle * (-solve middle column)) =
          ∑ middle, -(blocks.kII row middle * solve middle column) := by
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        rw [mul_neg]
      _ = -(∑ middle, blocks.kII row middle * solve middle column) := by
        rw [Finset.sum_neg_distrib]
  rw [hBoundaryTerm, hInteriorTerm,
    interiorSolve_columnEquation blocks solve hSolve row column]
  exact add_neg_cancel _

/-- Directed boundary maximum principle with an arbitrary common upper bound. -/
theorem interior_le_of_harmonic_boundary_le {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (bound : ℚ)
    (hBoundary : ∀ boundaryIndex, potential (Sum.inl boundaryIndex) ≤ bound)
    (hHarmonic : IsInteriorHarmonic blocks potential) :
    ∀ interiorIndex, potential (Sum.inr interiorIndex) ≤ bound := by
  have hUnivNonempty :
      (Finset.univ : Finset (CutVertex boundary interior)).Nonempty :=
    ⟨Sum.inl distinguished, Finset.mem_univ _⟩
  obtain ⟨maximumVertex, _hMaximumVertexMem, hMaximumOnUniv⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (CutVertex boundary interior))
      potential hUnivNonempty
  have hMaximum :
      ∀ vertex, potential vertex ≤ potential maximumVertex := by
    intro vertex
    exact hMaximumOnUniv vertex (Finset.mem_univ vertex)
  have hMaximumLe : potential maximumVertex ≤ bound := by
    cases maximumVertex with
    | inl boundaryIndex =>
        exact hBoundary boundaryIndex
    | inr interiorIndex =>
        obtain ⟨boundaryIndex, path⟩ :=
          hypotheses.everyInteriorReachesBoundary interiorIndex
        have hPropagation :
            potential (Sum.inl boundaryIndex) =
              potential (Sum.inr interiorIndex) :=
          maximum_propagates_to_boundary blocks distinguished hypotheses path
            potential hHarmonic hMaximum
        rw [← hPropagation]
        exact hBoundary boundaryIndex
  intro interiorIndex
  exact le_trans (hMaximum (Sum.inr interiorIndex)) hMaximumLe

/-- Directed boundary minimum principle with an arbitrary common lower bound. -/
theorem interior_ge_of_harmonic_boundary_ge {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (bound : ℚ)
    (hBoundary : ∀ boundaryIndex, bound ≤ potential (Sum.inl boundaryIndex))
    (hHarmonic : IsInteriorHarmonic blocks potential) :
    ∀ interiorIndex, bound ≤ potential (Sum.inr interiorIndex) := by
  have hNegBoundary :
      ∀ boundaryIndex,
        (-potential (Sum.inl boundaryIndex)) ≤ -bound := by
    intro boundaryIndex
    exact neg_le_neg (hBoundary boundaryIndex)
  have hNegHarmonic :
      IsInteriorHarmonic blocks (fun vertex => -potential vertex) := by
    intro interiorIndex
    rw [laplacianAction_neg, hHarmonic interiorIndex, neg_zero]
  intro interiorIndex
  have hNegUpper :=
    interior_le_of_harmonic_boundary_le
      blocks distinguished hypotheses (fun vertex => -potential vertex)
      (-bound) hNegBoundary hNegHarmonic interiorIndex
  have hReversed := neg_le_neg hNegUpper
  rw [neg_neg, neg_neg] at hReversed
  exact hReversed

/-- Every full harmonic basis potential is pointwise nonnegative. -/
theorem harmonicBasisPotential_nonnegative {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve)
    (column : Fin boundary) :
    ∀ vertex, 0 ≤ harmonicBasisPotential solve column vertex := by
  intro vertex
  cases vertex with
  | inl row =>
      exact boundaryBasis_nonnegative column row
  | inr row =>
      exact interior_ge_of_harmonic_boundary_ge
        blocks distinguished hypotheses (harmonicBasisPotential solve column) 0
        (fun boundaryIndex => boundaryBasis_nonnegative column boundaryIndex)
        (harmonicBasisPotential_isInteriorHarmonic blocks solve hSolve column)
        row

/-- Every full harmonic basis potential is pointwise at most one. -/
theorem harmonicBasisPotential_le_one {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve)
    (column : Fin boundary) :
    ∀ vertex, harmonicBasisPotential solve column vertex ≤ 1 := by
  intro vertex
  cases vertex with
  | inl row =>
      exact boundaryBasis_le_one column row
  | inr row =>
      exact interior_le_of_harmonic_boundary_le
        blocks distinguished hypotheses (harmonicBasisPotential solve column) 1
        (fun boundaryIndex => boundaryBasis_le_one column boundaryIndex)
        (harmonicBasisPotential_isInteriorHarmonic blocks solve hSolve column)
        row

/-- One proof-layer response entry is the boundary Laplacian action of the
    corresponding harmonic basis potential. -/
theorem mathlibResponse_entry_eq_laplacianAction_harmonicBasis
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary)
    (row column : Fin boundary) :
    mathlibResponseFromSolve blocks solve row column =
      laplacianAction blocks (harmonicBasisPotential solve column)
        (Sum.inl row) := by
  unfold mathlibResponseFromSolve laplacianAction
  rw [Fintype.sum_sum_type]
  change
    blocks.kBB row column -
        (∑ middle, blocks.kBI row middle * solve middle column) =
      (∑ boundaryIndex,
        blocks.kBB row boundaryIndex * boundaryBasis column boundaryIndex) +
      (∑ middle, blocks.kBI row middle * (-solve middle column))
  have hBoundaryTerm :
      (∑ boundaryIndex,
        blocks.kBB row boundaryIndex * boundaryBasis column boundaryIndex) =
        blocks.kBB row column := by
    calc
      (∑ boundaryIndex,
          blocks.kBB row boundaryIndex * boundaryBasis column boundaryIndex) =
          ∑ boundaryIndex,
            if boundaryIndex = column then blocks.kBB row boundaryIndex else 0 := by
        apply Finset.sum_congr rfl
        intro boundaryIndex _hBoundaryIndex
        by_cases hIndex : boundaryIndex = column
        · rw [boundaryBasis, if_pos hIndex, if_pos hIndex, mul_one]
        · rw [boundaryBasis, if_neg hIndex, if_neg hIndex, mul_zero]
      _ = blocks.kBB row column := by
        exact Fintype.sum_ite_eq' column (fun boundaryIndex => blocks.kBB row boundaryIndex)
  have hInteriorTerm :
      (∑ middle, blocks.kBI row middle * (-solve middle column)) =
        -(∑ middle, blocks.kBI row middle * solve middle column) := by
    calc
      (∑ middle, blocks.kBI row middle * (-solve middle column)) =
          ∑ middle, -(blocks.kBI row middle * solve middle column) := by
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        rw [mul_neg]
      _ = -(∑ middle, blocks.kBI row middle * solve middle column) := by
        rw [Finset.sum_neg_distrib]
  rw [hBoundaryTerm, hInteriorTerm]
  ring

/-- S08 off-diagonal sign theorem for every exact response representative. -/
theorem responseOffDiagonalNonpositive {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (response : ExactFractionMatrix boundary boundary)
    (hResponse : IsSchurDtnResponse blocks response) :
    ResponseOffDiagonalNonpositive response := by
  intro row column hRowColumn
  obtain ⟨solve, hSolve, hAgreement⟩ :=
    responseRepresentativeAgreement blocks response hResponse
  have hEntryAgreement := congrFun (congrFun hAgreement row) column
  change
    exactFractionValue (response row column) =
      mathlibResponseFromSolve blocks solve row column at hEntryAgreement
  rw [hEntryAgreement]
  rw [mathlibResponse_entry_eq_laplacianAction_harmonicBasis]
  unfold laplacianAction
  apply Finset.sum_nonpos
  intro target _hTargetMem
  by_cases hTarget : target = Sum.inl row
  · subst target
    change
      blockEntry blocks (Sum.inl row) (Sum.inl row) *
          boundaryBasis column row ≤ 0
    rw [boundaryBasis, if_neg hRowColumn, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg
      (hypotheses.offDiagonalNonpositive
        (Sum.inl row) target (Ne.symm hTarget))
      (harmonicBasisPotential_nonnegative
        blocks distinguished hypotheses solve hSolve column target)

/-- Row sum of the interior solve is exactly `-1`.  This is the finite
    algebraic form of constant-boundary harmonic extension. -/
theorem interiorSolve_rowSum_eq_neg_one {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve) :
    ∀ row, (∑ column, solve row column) = -1 := by
  have hResidualKernel :
      IsInteriorKernelVector blocks
        (fun middle => (∑ column, solve middle column) + 1) := by
    intro row
    calc
      (∑ middle,
          blocks.kII row middle * ((∑ column, solve middle column) + 1)) =
          ∑ middle,
            ((∑ column, blocks.kII row middle * solve middle column) +
              blocks.kII row middle) := by
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        calc
          blocks.kII row middle * ((∑ column, solve middle column) + 1) =
              blocks.kII row middle * (∑ column, solve middle column) +
                blocks.kII row middle * 1 := by
            rw [mul_add]
          _ = (∑ column, blocks.kII row middle * solve middle column) +
                blocks.kII row middle := by
            rw [Finset.mul_sum, mul_one]
      _ =
          (∑ middle, ∑ column,
            blocks.kII row middle * solve middle column) +
          ∑ middle, blocks.kII row middle := by
        rw [Finset.sum_add_distrib]
      _ =
          (∑ column, ∑ middle,
            blocks.kII row middle * solve middle column) +
          ∑ middle, blocks.kII row middle := by
        rw [Finset.sum_comm]
      _ =
          (∑ column, blocks.kIB row column) +
          ∑ middle, blocks.kII row middle := by
        have hColumnSum :
            (∑ column, ∑ middle,
              blocks.kII row middle * solve middle column) =
              ∑ column, blocks.kIB row column := by
          apply Finset.sum_congr rfl
          intro column _hColumn
          exact interiorSolve_columnEquation blocks solve hSolve row column
        rw [hColumnSum]
      _ = 0 := by
        have hRowConservative :=
          hypotheses.rowConservative (Sum.inr row)
        rw [Fintype.sum_sum_type] at hRowConservative
        change
          (∑ column, blocks.kIB row column) +
            (∑ middle, blocks.kII row middle) = 0 at hRowConservative
        exact hRowConservative
  have hResidualZero :=
    interiorKernelTrivial blocks distinguished hypotheses
      (fun middle => (∑ column, solve middle column) + 1)
      hResidualKernel
  intro row
  have hRowZero := congrFun hResidualZero row
  change (∑ column, solve row column) + 1 = 0 at hRowZero
  calc
    (∑ column, solve row column) =
        (∑ column, solve row column) + 1 - 1 := by
      ring
    _ = 0 - 1 := by
      rw [hRowZero]
    _ = -1 := by
      ring

/-- The proof-layer rational response has exact zero row sum. -/
theorem mathlibResponse_rowConservative {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve) :
    ∀ row, ∑ column, mathlibResponseFromSolve blocks solve row column = 0 := by
  intro row
  unfold mathlibResponseFromSolve
  change
    (∑ column,
      (blocks.kBB row column -
        ∑ middle, blocks.kBI row middle * solve middle column)) = 0
  rw [Finset.sum_sub_distrib]
  have hDoubleSum :
      (∑ column, ∑ middle,
        blocks.kBI row middle * solve middle column) =
        ∑ middle,
          blocks.kBI row middle * (∑ column, solve middle column) := by
    calc
      (∑ column, ∑ middle,
          blocks.kBI row middle * solve middle column) =
          ∑ middle, ∑ column,
            blocks.kBI row middle * solve middle column := by
        rw [Finset.sum_comm]
      _ = ∑ middle,
          blocks.kBI row middle * (∑ column, solve middle column) := by
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        rw [Finset.mul_sum]
  have hWeightedSum :
      (∑ middle,
        blocks.kBI row middle * (∑ column, solve middle column)) =
        -(∑ middle, blocks.kBI row middle) := by
    calc
      (∑ middle,
          blocks.kBI row middle * (∑ column, solve middle column)) =
          ∑ middle, blocks.kBI row middle * (-1) := by
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        rw [interiorSolve_rowSum_eq_neg_one
          blocks distinguished hypotheses solve hSolve middle]
      _ = ∑ middle, -(blocks.kBI row middle) := by
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        ring
      _ = -(∑ middle, blocks.kBI row middle) := by
        rw [Finset.sum_neg_distrib]
  rw [hDoubleSum, hWeightedSum, sub_neg_eq_add]
  have hRowConservative := hypotheses.rowConservative (Sum.inl row)
  rw [Fintype.sum_sum_type] at hRowConservative
  change
    (∑ column, blocks.kBB row column) +
      (∑ middle, blocks.kBI row middle) = 0 at hRowConservative
  exact hRowConservative

/-- S08 row-conservation theorem for every exact response representative. -/
theorem responseRowConservative {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (response : ExactFractionMatrix boundary boundary)
    (hResponse : IsSchurDtnResponse blocks response) :
    ResponseRowConservative response := by
  intro row
  obtain ⟨solve, hSolve, hAgreement⟩ :=
    responseRepresentativeAgreement blocks response hResponse
  calc
    (∑ column, exactFractionValue (response row column)) =
        ∑ column, mathlibResponseFromSolve blocks solve row column := by
      apply Finset.sum_congr rfl
      intro column _hColumn
      exact congrFun (congrFun hAgreement row) column
    _ = 0 :=
      mathlibResponse_rowConservative
        blocks distinguished hypotheses solve hSolve row

/-- Off-diagonal nonpositivity plus zero row sum force nonnegative diagonal. -/
theorem responseDiagonalNonnegative_of_offDiagonal_rowConservative
    {boundary : Nat}
    (response : ExactFractionMatrix boundary boundary)
    (hOffDiagonal : ResponseOffDiagonalNonpositive response)
    (hRowConservative : ResponseRowConservative response) :
    ResponseDiagonalNonnegative response := by
  intro row
  let value : Fin boundary → ℚ :=
    fun column => exactFractionValue (response row column)
  have hOffDiagonalSum :
      (∑ column ∈ ({row}ᶜ : Finset (Fin boundary)), value column) ≤ 0 := by
    apply Finset.sum_nonpos
    intro column hColumn
    have hNotSingleton : column ∉ ({row} : Finset (Fin boundary)) :=
      Finset.mem_compl.mp hColumn
    have hColumnNe : column ≠ row := by
      intro hEquality
      subst column
      exact hNotSingleton (Finset.mem_singleton_self row)
    exact hOffDiagonal row column (Ne.symm hColumnNe)
  have hRowZero := hRowConservative row
  change (∑ column, value column) = 0 at hRowZero
  rw [Fintype.sum_eq_add_sum_compl row value] at hRowZero
  change 0 ≤ value row
  have hDiagonalEquality :
      value row =
        -(∑ column ∈ ({row}ᶜ : Finset (Fin boundary)), value column) := by
    calc
      value row =
          value row +
            (∑ column ∈ ({row}ᶜ : Finset (Fin boundary)), value column) -
            (∑ column ∈ ({row}ᶜ : Finset (Fin boundary)), value column) := by
        ring
      _ =
          0 - (∑ column ∈ ({row}ᶜ : Finset (Fin boundary)), value column) := by
        rw [hRowZero]
      _ =
          -(∑ column ∈ ({row}ᶜ : Finset (Fin boundary)), value column) := by
        ring
  rw [hDiagonalEquality]
  exact neg_nonneg.mpr hOffDiagonalSum

/-- S08 diagonal nonnegativity for every exact response representative. -/
theorem responseDiagonalNonnegative {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (response : ExactFractionMatrix boundary boundary)
    (hResponse : IsSchurDtnResponse blocks response) :
    ResponseDiagonalNonnegative response :=
  responseDiagonalNonnegative_of_offDiagonal_rowConservative response
    (responseOffDiagonalNonpositive
      blocks distinguished hypotheses response hResponse)
    (responseRowConservative
      blocks distinguished hypotheses response hResponse)

/-- S08 closes the directed Laplace/Z-matrix response contract, but not strict
    distinguished-port positivity. -/
theorem directedLaplacianClosure {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished) :
    ∀ response,
      IsSchurDtnResponse blocks response →
      IsDirectedLaplacianResponse response := by
  intro response hResponse
  exact
    ⟨responseOffDiagonalNonpositive
        blocks distinguished hypotheses response hResponse,
      responseRowConservative
        blocks distinguished hypotheses response hResponse,
      responseDiagonalNonnegative
        blocks distinguished hypotheses response hResponse⟩

end CNNAProofs.P001
