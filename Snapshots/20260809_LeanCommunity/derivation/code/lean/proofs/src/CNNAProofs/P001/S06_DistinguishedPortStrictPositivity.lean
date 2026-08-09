import CNNAProofs.P001.S05_ResponseDirectedLaplacian

/-!
# P001 — S09 strict distinguished-port positivity

This module closes the remaining generic analytical component of P001.  The
argument is a strict directed maximum-principle proof on the original ordered
C006 blocks.

For the harmonic basis potential equal to one at the distinguished boundary
port and zero at every other boundary port, suppose that the distinguished
boundary action were zero.  Row conservation and off-diagonal nonpositivity
then make every maximum-defect term nonnegative with zero total sum.  Hence the
value one propagates across every positive outgoing arc.  Interior harmonicity
continues the propagation along the positive path supplied by
`distinguishedReachesOtherBoundary`, forcing value one at a different boundary
port, where the basis value is definitionally zero.  This contradiction makes
the distinguished boundary action nonzero; S08 nonnegativity then upgrades it
to strict positivity.

No symmetry, Hermitian positivity, inverse, determinant, regularizer,
pseudoinverse, selected solver, or grounding vertex is introduced.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- The boundary analogue of interior maximum propagation.  If the
    distinguished boundary row has zero Laplacian action at a global maximum,
    the maximum propagates across every positive outgoing arc. -/
theorem maximum_propagates_from_distinguished_boundary_across_positive_arc
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (potential : CutPotential boundary interior)
    (target : CutVertex boundary interior)
    (hHarmonicAtDistinguished :
      laplacianAction blocks potential (Sum.inl distinguished) = 0)
    (hMaximum :
      ∀ vertex, potential vertex ≤ potential (Sum.inl distinguished))
    (hArc : PositiveArc blocks (Sum.inl distinguished) target) :
    potential target = potential (Sum.inl distinguished) := by
  have hDefectSum :
      ∑ vertex,
        maximumDefectTerm blocks potential (Sum.inl distinguished) vertex = 0 :=
    maximumDefectSum_eq_zero blocks potential (Sum.inl distinguished)
      (hypotheses.rowConservative (Sum.inl distinguished))
      hHarmonicAtDistinguished
  have hAllDefectsZero :
      ∀ vertex ∈ (Finset.univ : Finset (CutVertex boundary interior)),
        maximumDefectTerm blocks potential (Sum.inl distinguished) vertex = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun vertex _hVertex =>
        maximumDefectTerm_nonnegative blocks potential
          (Sum.inl distinguished) vertex
          hypotheses.offDiagonalNonpositive hMaximum)).mp hDefectSum
  have hTargetDefect :
      maximumDefectTerm blocks potential (Sum.inl distinguished) target = 0 :=
    hAllDefectsZero target (Finset.mem_univ target)
  unfold maximumDefectTerm at hTargetDefect
  have hWeightPositive :
      0 < -blockEntry blocks (Sum.inl distinguished) target :=
    neg_pos.mpr hArc.2
  have hWeightNonzero :
      -blockEntry blocks (Sum.inl distinguished) target ≠ 0 :=
    ne_of_gt hWeightPositive
  rcases mul_eq_zero.mp hTargetDefect with hWeightZero | hDifferenceZero
  · exact False.elim (hWeightNonzero hWeightZero)
  · exact (sub_eq_zero.mp hDifferenceZero).symm

/-- For the distinguished harmonic basis potential, value one propagates
    across one positive arc from any source already known to have value one.
    A boundary source with value one must be the distinguished port; an
    interior source uses the existing interior maximum-propagation theorem. -/
theorem harmonicBasis_one_propagates_across_positive_arc
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve)
    (hDistinguishedActionZero :
      laplacianAction blocks
        (harmonicBasisPotential solve distinguished)
        (Sum.inl distinguished) = 0)
    {source target : CutVertex boundary interior}
    (hSourceOne : harmonicBasisPotential solve distinguished source = 1)
    (hArc : PositiveArc blocks source target) :
    harmonicBasisPotential solve distinguished target = 1 := by
  have hUpper :
      ∀ vertex,
        harmonicBasisPotential solve distinguished vertex ≤ 1 :=
    harmonicBasisPotential_le_one
      blocks distinguished hypotheses solve hSolve distinguished
  have hInteriorHarmonic :
      IsInteriorHarmonic blocks
        (harmonicBasisPotential solve distinguished) :=
    harmonicBasisPotential_isInteriorHarmonic
      blocks solve hSolve distinguished
  cases source with
  | inl boundaryIndex =>
      by_cases hBoundary : boundaryIndex = distinguished
      · subst boundaryIndex
        have hMaximum :
            ∀ vertex,
              harmonicBasisPotential solve distinguished vertex ≤
                harmonicBasisPotential solve distinguished
                  (Sum.inl distinguished) := by
          intro vertex
          rw [hSourceOne]
          exact hUpper vertex
        have hStep :=
          maximum_propagates_from_distinguished_boundary_across_positive_arc
            blocks distinguished hypotheses
            (harmonicBasisPotential solve distinguished) target
            hDistinguishedActionZero hMaximum hArc
        exact hStep.trans hSourceOne
      · have hBoundaryZero :
            harmonicBasisPotential solve distinguished
                (Sum.inl boundaryIndex) = 0 := by
          change boundaryBasis distinguished boundaryIndex = 0
          rw [boundaryBasis, if_neg hBoundary]
        have hImpossible : (0 : ℚ) = 1 :=
          hBoundaryZero.symm.trans hSourceOne
        exact False.elim (zero_ne_one hImpossible)
  | inr interiorIndex =>
      have hMaximum :
          ∀ vertex,
            harmonicBasisPotential solve distinguished vertex ≤
              harmonicBasisPotential solve distinguished
                (Sum.inr interiorIndex) := by
        intro vertex
        rw [hSourceOne]
        exact hUpper vertex
      have hStep :=
        maximum_propagates_across_positive_arc
          blocks distinguished hypotheses
          (harmonicBasisPotential solve distinguished)
          interiorIndex target
          (hInteriorHarmonic interiorIndex) hMaximum hArc
      exact hStep.trans hSourceOne

/-- Under zero distinguished action, the value one would propagate along every
    positive path starting at the distinguished boundary port. -/
theorem harmonicBasis_one_propagates_along_positive_path
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve)
    (hDistinguishedActionZero :
      laplacianAction blocks
        (harmonicBasisPotential solve distinguished)
        (Sum.inl distinguished) = 0) :
    ∀ {source target},
      PositivePath blocks source target →
      harmonicBasisPotential solve distinguished source = 1 →
      harmonicBasisPotential solve distinguished target = 1 := by
  intro source target path hSourceOne
  induction path with
  | edge hArc =>
      exact harmonicBasis_one_propagates_across_positive_arc
        blocks distinguished hypotheses solve hSolve
        hDistinguishedActionZero hSourceOne hArc
  | tail _hPrefix hArc hMiddleOne =>
      exact harmonicBasis_one_propagates_across_positive_arc
        blocks distinguished hypotheses solve hSolve
        hDistinguishedActionZero hMiddleOne hArc

/-- The distinguished harmonic basis function cannot have zero boundary action:
    the required path to another boundary port would otherwise carry the value
    one to a point where the boundary basis is zero. -/
theorem harmonicBasis_distinguished_action_ne_zero
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (solve : RationalMatrix interior boundary)
    (hSolve : IsMathlibInteriorSolve blocks solve) :
    laplacianAction blocks
      (harmonicBasisPotential solve distinguished)
      (Sum.inl distinguished) ≠ 0 := by
  intro hActionZero
  obtain ⟨other, hOther, path⟩ :=
    hypotheses.distinguishedReachesOtherBoundary
  have hDistinguishedOne :
      harmonicBasisPotential solve distinguished
          (Sum.inl distinguished) = 1 := by
    change boundaryBasis distinguished distinguished = 1
    rw [boundaryBasis, if_pos rfl]
  have hOtherOne :
      harmonicBasisPotential solve distinguished (Sum.inl other) = 1 :=
    harmonicBasis_one_propagates_along_positive_path
      blocks distinguished hypotheses solve hSolve hActionZero
      path hDistinguishedOne
  have hOtherZero :
      harmonicBasisPotential solve distinguished (Sum.inl other) = 0 := by
    change boundaryBasis distinguished other = 0
    rw [boundaryBasis, if_neg hOther]
  have hImpossible : (0 : ℚ) = 1 :=
    hOtherZero.symm.trans hOtherOne
  exact zero_ne_one hImpossible

/-- Every exact response representative has a nonzero distinguished diagonal
    value under the generic P001 cut hypotheses. -/
theorem distinguishedResponseDiagonal_ne_zero
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished)
    (response : ExactFractionMatrix boundary boundary)
    (hResponse : IsSchurDtnResponse blocks response) :
    exactFractionValue (response distinguished distinguished) ≠ 0 := by
  obtain ⟨solve, hSolve, hAgreement⟩ :=
    responseRepresentativeAgreement blocks response hResponse
  have hEntryAgreement :=
    congrFun (congrFun hAgreement distinguished) distinguished
  change
    exactFractionValue (response distinguished distinguished) =
      mathlibResponseFromSolve blocks solve distinguished distinguished
      at hEntryAgreement
  intro hResponseZero
  have hActionZero :
      laplacianAction blocks
        (harmonicBasisPotential solve distinguished)
        (Sum.inl distinguished) = 0 := by
    calc
      laplacianAction blocks
          (harmonicBasisPotential solve distinguished)
          (Sum.inl distinguished) =
          mathlibResponseFromSolve blocks solve
            distinguished distinguished :=
        (mathlibResponse_entry_eq_laplacianAction_harmonicBasis
          blocks solve distinguished distinguished).symm
      _ = exactFractionValue
          (response distinguished distinguished) :=
        hEntryAgreement.symm
      _ = 0 := hResponseZero
  exact harmonicBasis_distinguished_action_ne_zero
    blocks distinguished hypotheses solve hSolve hActionZero

/-- S09 strict positivity at the distinguished boundary port.  S08 supplies
    nonnegativity; the path/maximum-principle contradiction supplies nonzero. -/
theorem distinguishedPortStrictlyPositive
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished) :
    ∀ response,
      IsSchurDtnResponse blocks response →
      DistinguishedPortStrictlyPositive distinguished response := by
  intro response hResponse
  have hNonnegative :
      0 ≤ exactFractionValue (response distinguished distinguished) :=
    responseDiagonalNonnegative
      blocks distinguished hypotheses response hResponse distinguished
  have hNonzero :
      exactFractionValue (response distinguished distinguished) ≠ 0 :=
    distinguishedResponseDiagonal_ne_zero
      blocks distinguished hypotheses response hResponse
  exact lt_of_le_of_ne hNonnegative (Ne.symm hNonzero)

/-- S09 completes the generic reusable directed Schur/DtN/Kron closure. -/
theorem directedSchurDtnClosure
    {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary)
    (hypotheses : DirectedCutHypotheses blocks distinguished) :
    DirectedSchurDtnClosure blocks distinguished := by
  have hKernel : InteriorKernelTrivial blocks :=
    interiorKernelTrivial blocks distinguished hypotheses
  exact {
    semanticBridge := exactSemanticBridge blocks
    interiorSolveExists := interiorSolveExists blocks hKernel
    interiorSolveUnique := interiorSolveUnique blocks hKernel
    c006InteriorAdmissible := c006InteriorAdmissible blocks hKernel
    responseExists := responseExists blocks hKernel
    responseWitnessIndependent := responseWitnessIndependent blocks hKernel
    directedLaplacianClosure :=
      directedLaplacianClosure blocks distinguished hypotheses
    distinguishedPortPositive :=
      distinguishedPortStrictlyPositive blocks distinguished hypotheses }

/-- The generic P001 contract is now inhabited.  Canonical M001/C007
    instantiation remains a separate cut-specific handoff. -/
theorem reusableDirectedClosureContract : ReusableDirectedClosureContract := by
  intro boundary interior blocks distinguished hypotheses
  exact directedSchurDtnClosure blocks distinguished hypotheses

end CNNAProofs.P001
