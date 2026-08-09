import CNNAProofs.P001.S01_ExactSemanticBridge

/-!
# P001 — finite directed maximum principle

This module proves the analytical layer that precedes finite-dimensional
existence.  It works on the original ordered C006 blocks and introduces no
inverse, determinant, regularizer, pseudoinverse, symmetrization, or grounding
vertex.

The proof has four explicit stages:

1. rewrite the harmonic row equation as a sum of nonnegative maximum defects;
2. propagate a global maximum across every positive directed arc;
3. propagate it along an interior path to the first boundary hit;
4. apply the argument to a zero-boundary extension and to its negation.

The result is the triviality of the homogeneous interior kernel.  Surjectivity,
solve existence, and response closure remain separate later steps.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- Maximum defect contributed by one target to one source row. -/
def maximumDefectTerm {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (potential : CutPotential boundary interior)
    (source target : CutVertex boundary interior) : ℚ :=
  (-blockEntry blocks source target) *
    (potential source - potential target)

/-- The zero-boundary extension vanishes on every boundary coordinate. -/
theorem zeroBoundaryExtension_vanishesOnBoundary {boundary interior : Nat}
    (vector : Fin interior → ℚ) :
    VanishesOnBoundary (zeroBoundaryExtension (boundary := boundary) vector) := by
  intro boundaryIndex
  rfl

/-- Full interior action of a zero-boundary extension is exactly `K_II u`. -/
theorem laplacianAction_zeroBoundaryExtension {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (vector : Fin interior → ℚ)
    (row : Fin interior) :
    laplacianAction blocks (zeroBoundaryExtension (boundary := boundary) vector)
        (Sum.inr row) =
      ∑ column, blocks.kII row column * vector column := by
  unfold laplacianAction
  rw [Fintype.sum_sum_type]
  change
    (∑ boundaryIndex : Fin boundary, blocks.kIB row boundaryIndex * 0) +
        (∑ column : Fin interior, blocks.kII row column * vector column) =
      ∑ column : Fin interior, blocks.kII row column * vector column
  have hBoundarySum :
      (∑ boundaryIndex : Fin boundary,
        blocks.kIB row boundaryIndex * 0) = 0 := by
    apply Finset.sum_eq_zero
    intro boundaryIndex _hBoundaryIndex
    rw [mul_zero]
  rw [hBoundarySum, zero_add]

/-- A homogeneous interior vector yields an interior-harmonic full potential. -/
theorem zeroBoundaryExtension_isInteriorHarmonic {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (vector : Fin interior → ℚ)
    (hKernel : IsInteriorKernelVector blocks vector) :
    IsInteriorHarmonic blocks
      (zeroBoundaryExtension (boundary := boundary) vector) := by
  intro row
  rw [laplacianAction_zeroBoundaryExtension]
  exact hKernel row

/-- Laplacian action commutes with pointwise negation. -/
theorem laplacianAction_neg {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (potential : CutPotential boundary interior)
    (source : CutVertex boundary interior) :
    laplacianAction blocks (fun vertex => -potential vertex) source =
      -laplacianAction blocks potential source := by
  unfold laplacianAction
  calc
    (∑ target, blockEntry blocks source target * (-potential target)) =
        ∑ target, -(blockEntry blocks source target * potential target) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      rw [mul_neg]
    _ = -(∑ target, blockEntry blocks source target * potential target) := by
      rw [Finset.sum_neg_distrib]

/-- At a harmonic row, row conservation rewrites the equation as a zero sum of
    maximum-defect terms. -/
theorem maximumDefectSum_eq_zero {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (potential : CutPotential boundary interior)
    (source : CutVertex boundary interior)
    (hRowConservative : ∑ target, blockEntry blocks source target = 0)
    (hHarmonic : laplacianAction blocks potential source = 0) :
    ∑ target, maximumDefectTerm blocks potential source target = 0 := by
  unfold maximumDefectTerm
  calc
    (∑ target,
        (-blockEntry blocks source target) *
          (potential source - potential target)) =
        ∑ target,
          ((-blockEntry blocks source target) * potential source +
            blockEntry blocks source target * potential target) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      ring
    _ =
        (∑ target, -blockEntry blocks source target) * potential source +
          ∑ target, blockEntry blocks source target * potential target := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ =
        -(∑ target, blockEntry blocks source target) * potential source +
          laplacianAction blocks potential source := by
      rw [Finset.sum_neg_distrib]
      rfl
    _ = 0 := by
      rw [hRowConservative, hHarmonic, neg_zero, zero_mul, zero_add]

/-- Every maximum-defect term is nonnegative at a global maximum. -/
theorem maximumDefectTerm_nonnegative {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (potential : CutPotential boundary interior)
    (source target : CutVertex boundary interior)
    (hOffDiagonal :
      ∀ left right, left ≠ right → blockEntry blocks left right ≤ 0)
    (hMaximum : ∀ vertex, potential vertex ≤ potential source) :
    0 ≤ maximumDefectTerm blocks potential source target := by
  by_cases hTarget : target = source
  · subst target
    unfold maximumDefectTerm
    rw [sub_self, mul_zero]
  · unfold maximumDefectTerm
    exact mul_nonneg
      (neg_nonneg.mpr (hOffDiagonal source target (Ne.symm hTarget)))
      (sub_nonneg.mpr (hMaximum target))

/-- A global maximum at an interior harmonic source propagates across every
    positive outgoing arc. -/
theorem maximum_propagates_across_positive_arc {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (source : Fin interior)
    (target : CutVertex boundary interior)
    (hHarmonic :
      laplacianAction blocks potential (Sum.inr source) = 0)
    (hMaximum :
      ∀ vertex, potential vertex ≤ potential (Sum.inr source))
    (hArc : PositiveArc blocks (Sum.inr source) target) :
    potential target = potential (Sum.inr source) := by
  have hDefectSum :
      ∑ vertex,
        maximumDefectTerm blocks potential (Sum.inr source) vertex = 0 :=
    maximumDefectSum_eq_zero blocks potential (Sum.inr source)
      (hypotheses.rowConservative (Sum.inr source)) hHarmonic
  have hAllDefectsZero :
      ∀ vertex ∈ (Finset.univ : Finset (CutVertex boundary interior)),
        maximumDefectTerm blocks potential (Sum.inr source) vertex = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun vertex _hVertex =>
        maximumDefectTerm_nonnegative blocks potential (Sum.inr source) vertex
          hypotheses.offDiagonalNonpositive hMaximum)).mp hDefectSum
  have hTargetDefect :
      maximumDefectTerm blocks potential (Sum.inr source) target = 0 :=
    hAllDefectsZero target (Finset.mem_univ target)
  unfold maximumDefectTerm at hTargetDefect
  have hWeightPositive :
      0 < -blockEntry blocks (Sum.inr source) target :=
    neg_pos.mpr hArc.2
  have hWeightNonzero :
      -blockEntry blocks (Sum.inr source) target ≠ 0 :=
    ne_of_gt hWeightPositive
  rcases mul_eq_zero.mp hTargetDefect with hWeightZero | hDifferenceZero
  · exact False.elim (hWeightNonzero hWeightZero)
  · exact (sub_eq_zero.mp hDifferenceZero).symm

/-- A global interior maximum propagates along an interior first-hit path to
    its terminal boundary vertex. -/
theorem maximum_propagates_to_boundary {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished) :
    ∀ {source target},
      InteriorPathToBoundary blocks source target →
      ∀ potential : CutPotential boundary interior,
        IsInteriorHarmonic blocks potential →
        (∀ vertex, potential vertex ≤ potential (Sum.inr source)) →
        potential (Sum.inl target) = potential (Sum.inr source) := by
  intro source target path
  refine InteriorPathToBoundary.rec
    (motive := fun pathSource pathTarget _ =>
      ∀ potential : CutPotential boundary interior,
        IsInteriorHarmonic blocks potential →
        (∀ vertex, potential vertex ≤ potential (Sum.inr pathSource)) →
        potential (Sum.inl pathTarget) = potential (Sum.inr pathSource))
    ?_ ?_ path
  · intro pathSource pathTarget hArc potential hInteriorHarmonic hMaximum
    exact maximum_propagates_across_positive_arc
      blocks distinguished hypotheses potential pathSource (Sum.inl pathTarget)
      (hInteriorHarmonic pathSource) hMaximum hArc
  · intro pathSource middle pathTarget hArc tail inductionHypothesis potential hInteriorHarmonic hMaximum
    have hStep :
        potential (Sum.inr middle) = potential (Sum.inr pathSource) :=
      maximum_propagates_across_positive_arc
        blocks distinguished hypotheses potential pathSource (Sum.inr middle)
        (hInteriorHarmonic pathSource) hMaximum hArc
    have hMaximumAtMiddle :
        ∀ vertex, potential vertex ≤ potential (Sum.inr middle) := by
      intro vertex
      rw [hStep]
      exact hMaximum vertex
    have hTail :
        potential (Sum.inl pathTarget) = potential (Sum.inr middle) :=
      inductionHypothesis potential hInteriorHarmonic hMaximumAtMiddle
    exact hTail.trans hStep

/-- Zero boundary data force every interior harmonic value to be nonpositive. -/
theorem interior_le_zero_of_harmonic_zero_boundary {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (hBoundary : VanishesOnBoundary potential)
    (hHarmonic : IsInteriorHarmonic blocks potential) :
    ∀ interiorIndex, potential (Sum.inr interiorIndex) ≤ 0 := by
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
  have hMaximumZero : potential maximumVertex = 0 := by
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
        exact hPropagation.symm.trans (hBoundary boundaryIndex)
  intro interiorIndex
  have hBound := hMaximum (Sum.inr interiorIndex)
  rw [hMaximumZero] at hBound
  exact hBound

/-- Zero boundary data force every interior harmonic value to be nonnegative. -/
theorem interior_nonnegative_of_harmonic_zero_boundary
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (hBoundary : VanishesOnBoundary potential)
    (hHarmonic : IsInteriorHarmonic blocks potential) :
    ∀ interiorIndex, 0 ≤ potential (Sum.inr interiorIndex) := by
  have hNegBoundary :
      VanishesOnBoundary (fun vertex => -potential vertex) := by
    intro boundaryIndex
    change -potential (Sum.inl boundaryIndex) = 0
    rw [hBoundary boundaryIndex, neg_zero]
  have hNegHarmonic :
      IsInteriorHarmonic blocks (fun vertex => -potential vertex) := by
    intro interiorIndex
    rw [laplacianAction_neg, hHarmonic interiorIndex, neg_zero]
  intro interiorIndex
  have hNegNonpositive :=
    interior_le_zero_of_harmonic_zero_boundary
      blocks distinguished hypotheses (fun vertex => -potential vertex)
      hNegBoundary hNegHarmonic interiorIndex
  exact neg_nonpos.mp hNegNonpositive

/-- Directed discrete maximum principle for homogeneous zero-boundary data. -/
theorem interior_eq_zero_of_harmonic_zero_boundary {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (hBoundary : VanishesOnBoundary potential)
    (hHarmonic : IsInteriorHarmonic blocks potential) :
    ∀ interiorIndex, potential (Sum.inr interiorIndex) = 0 := by
  intro interiorIndex
  exact le_antisymm
    (interior_le_zero_of_harmonic_zero_boundary
      blocks distinguished hypotheses potential hBoundary hHarmonic interiorIndex)
    (interior_nonnegative_of_harmonic_zero_boundary
      blocks distinguished hypotheses potential hBoundary hHarmonic interiorIndex)

/-- The original unregularized interior block has trivial kernel. -/
theorem interiorKernelTrivial {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished) :
    InteriorKernelTrivial blocks := by
  intro vector hKernel
  apply funext
  intro interiorIndex
  exact interior_eq_zero_of_harmonic_zero_boundary
    blocks distinguished hypotheses
    (zeroBoundaryExtension (boundary := boundary) vector)
    (zeroBoundaryExtension_vanishesOnBoundary
      (boundary := boundary) vector)
    (zeroBoundaryExtension_isInteriorHarmonic blocks vector hKernel)
    interiorIndex

end CNNAProofs.P001
