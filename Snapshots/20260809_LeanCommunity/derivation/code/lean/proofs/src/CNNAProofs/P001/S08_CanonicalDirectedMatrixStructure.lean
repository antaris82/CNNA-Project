import CNNAProofs.P001.S07_CanonicalBirthCutInstantiation

/-!
# P001 R6B.1 — exact directed-matrix structure of the canonical C007 cut

This module proves the two algebraic fields of `DirectedCutHypotheses` directly
from the C005 conductance list and the C007 source/out-degree matrix assembly.
It keeps the exact-fraction fold visible and uses only the C007 representation
relation to transfer the result to an arbitrary canonical-rational block
realization.

No symmetry, inverse, regularization, grounding vertex, or additional graph
hypothesis is introduced.  Conductance-pair uniqueness is not needed for the
sign and row-conservation claims: repeated positive entries would still add in
the same ordered pair and preserve both statements.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive
open CanonicalBirthLocalMeasurementCut
open NextOpenProvenanceSlot
open InterBirthDirectedResponse

/-- Address carried by one coordinate of the ordered M001 boundary/interior sum. -/
def canonicalCutAddress {X : ResponseCapableState} (next : NextOpenSlot X) :
    CutVertex (boundary next).length
      (CanonicalBirthLocalMeasurementCut.interior next).length →
      ProvenanceAddress X.grammar.branching
  | Sum.inl index => boundaryAddress next index
  | Sum.inr index => interiorAddress next index

/-- The ordered M001 sum coordinate map is injective.  Duplicate-freeness within
one block and boundary/interior disjointness handle the three cases explicitly. -/
theorem canonicalCutAddress_injective {X : ResponseCapableState}
    (next : NextOpenSlot X) : Function.Injective (canonicalCutAddress next) := by
  intro left right hAddress
  cases left with
  | inl leftBoundary =>
      cases right with
      | inl rightBoundary =>
          have hIndex : leftBoundary = rightBoundary :=
            (boundary_nodup next).injective_get hAddress
          exact congrArg Sum.inl hIndex
      | inr rightInterior =>
          have hBoundary : boundaryAddress next leftBoundary ∈ boundary next :=
            List.get_mem (boundary next) leftBoundary
          have hInterior : interiorAddress next rightInterior ∈
              CanonicalBirthLocalMeasurementCut.interior next :=
            List.get_mem (CanonicalBirthLocalMeasurementCut.interior next) rightInterior
          have hInteriorAtBoundary : boundaryAddress next leftBoundary ∈
              CanonicalBirthLocalMeasurementCut.interior next := by
            change boundaryAddress next leftBoundary =
              interiorAddress next rightInterior at hAddress
            rw [hAddress]
            exact hInterior
          exact False.elim
            (boundary_interior_disjoint next
              (boundaryAddress next leftBoundary)
              hBoundary hInteriorAtBoundary)
  | inr leftInterior =>
      cases right with
      | inl rightBoundary =>
          have hInterior : interiorAddress next leftInterior ∈
              CanonicalBirthLocalMeasurementCut.interior next :=
            List.get_mem (CanonicalBirthLocalMeasurementCut.interior next) leftInterior
          have hBoundary : boundaryAddress next rightBoundary ∈ boundary next :=
            List.get_mem (boundary next) rightBoundary
          have hInteriorAtBoundary : boundaryAddress next rightBoundary ∈
              CanonicalBirthLocalMeasurementCut.interior next := by
            change interiorAddress next leftInterior =
              boundaryAddress next rightBoundary at hAddress
            rw [← hAddress]
            exact hInterior
          exact False.elim
            (boundary_interior_disjoint next
              (boundaryAddress next rightBoundary)
              hBoundary hInteriorAtBoundary)
      | inr rightInterior =>
          have hIndex : leftInterior = rightInterior :=
            (interior_nodup next).injective_get hAddress
          exact congrArg Sum.inr hIndex

/-- Every address in the born canonical carrier has one coordinate in the M001
sum order. -/
theorem canonicalCutCoordinate_exists {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {address : ProvenanceAddress X.grammar.branching}
    (hCarrier : address ∈ canonicalCarrier X) :
    ∃ coordinate, canonicalCutAddress next coordinate = address := by
  cases carrier_covered next address hCarrier with
  | inl hBoundary =>
      obtain ⟨index, hIndex⟩ := List.get_of_mem hBoundary
      exact ⟨Sum.inl index, hIndex⟩
  | inr hInterior =>
      obtain ⟨index, hIndex⟩ := List.get_of_mem hInterior
      exact ⟨Sum.inr index, hIndex⟩

/-- Every endpoint of a stored C005 conductance has an M001 sum coordinate. -/
theorem conductanceSourceCoordinate_exists {X : ResponseCapableState}
    (next : NextOpenSlot X) (edge : DirectedConductance X.grammar.branching)
    (hEdge : edge ∈ X.conductances) :
    ∃ coordinate, canonicalCutAddress next coordinate = edge.source := by
  have hBorn := (X.conductanceEndpointsBorn edge hEdge).1
  exact canonicalCutCoordinate_exists next (born_implies_carrier_mem hBorn)

/-- Target-coordinate counterpart of `conductanceSourceCoordinate_exists`. -/
theorem conductanceTargetCoordinate_exists {X : ResponseCapableState}
    (next : NextOpenSlot X) (edge : DirectedConductance X.grammar.branching)
    (hEdge : edge ∈ X.conductances) :
    ∃ coordinate, canonicalCutAddress next coordinate = edge.target := by
  have hBorn := (X.conductanceEndpointsBorn edge hEdge).2
  exact canonicalCutCoordinate_exists next (born_implies_carrier_mem hBorn)

/-- Rational recursive outgoing sum used only as a transparent semantic normal
form for C007's exact-fraction fold. -/
def ratOutgoingSum {b : BranchingParameter} :
    List (DirectedConductance b) → ProvenanceAddress b → ℚ
  | [], _source => 0
  | edge :: edges, source =>
      (if edge.source = source then edge.value else 0) +
        ratOutgoingSum edges source

/-- Rational recursive ordered-pair sum corresponding to the C007 fold. -/
def ratOrderedPairSum {b : BranchingParameter} :
    List (DirectedConductance b) →
      ProvenanceAddress b → ProvenanceAddress b → ℚ
  | [], _source, _target => 0
  | edge :: edges, source, target =>
      (if edge.source = source then
        if edge.target = target then edge.value else 0
      else 0) + ratOrderedPairSum edges source target

/-- Rational value commutes with C007's outgoing exact-fraction list fold. -/
theorem exactFractionValue_outgoingFold {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source : ProvenanceAddress b) (initial : ExactFraction) :
    exactFractionValue
        (edges.foldl
          (fun accumulator edge =>
            if edge.source = source then
              ExactFraction.add accumulator (ExactFraction.ofRat edge.value)
            else accumulator)
          initial) =
      exactFractionValue initial + ratOutgoingSum edges source := by
  induction edges generalizing initial with
  | nil =>
      change exactFractionValue initial = exactFractionValue initial + 0
      rw [add_zero]
  | cons edge edges ih =>
      change
        exactFractionValue
            (edges.foldl
              (fun accumulator edge =>
                if edge.source = source then
                  ExactFraction.add accumulator (ExactFraction.ofRat edge.value)
                else accumulator)
              (if edge.source = source then
                ExactFraction.add initial (ExactFraction.ofRat edge.value)
              else initial)) =
          exactFractionValue initial +
            ((if edge.source = source then edge.value else 0) +
              ratOutgoingSum edges source)
      by_cases hSource : edge.source = source
      · rw [if_pos hSource, if_pos hSource]
        rw [ih, exactFractionValue_add, exactFractionValue_ofRat]
        ring
      · rw [if_neg hSource, if_neg hSource]
        rw [ih, zero_add]

/-- Rational value commutes with C007's ordered-pair exact-fraction list fold. -/
theorem exactFractionValue_orderedPairFold {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) (initial : ExactFraction) :
    exactFractionValue
        (edges.foldl
          (fun accumulator edge =>
            if edge.source = source then
              if edge.target = target then
                ExactFraction.add accumulator (ExactFraction.ofRat edge.value)
              else accumulator
            else accumulator)
          initial) =
      exactFractionValue initial + ratOrderedPairSum edges source target := by
  induction edges generalizing initial with
  | nil =>
      change exactFractionValue initial = exactFractionValue initial + 0
      rw [add_zero]
  | cons edge edges ih =>
      change
        exactFractionValue
            (edges.foldl
              (fun accumulator edge =>
                if edge.source = source then
                  if edge.target = target then
                    ExactFraction.add accumulator (ExactFraction.ofRat edge.value)
                  else accumulator
                else accumulator)
              (if edge.source = source then
                if edge.target = target then
                  ExactFraction.add initial (ExactFraction.ofRat edge.value)
                else initial
              else initial)) =
          exactFractionValue initial +
            ((if edge.source = source then
                if edge.target = target then edge.value else 0
              else 0) + ratOrderedPairSum edges source target)
      by_cases hSource : edge.source = source
      · rw [if_pos hSource, if_pos hSource]
        by_cases hTarget : edge.target = target
        · rw [if_pos hTarget, if_pos hTarget]
          rw [ih, exactFractionValue_add, exactFractionValue_ofRat]
          ring
        · rw [if_neg hTarget, if_neg hTarget]
          rw [ih, zero_add]
      · rw [if_neg hSource, if_neg hSource]
        rw [ih, zero_add]

/-- Exact C007 outgoing sum has the recursive rational value above. -/
theorem exactFractionValue_outgoingSum {b : BranchingParameter}
    (edges : List (DirectedConductance b)) (source : ProvenanceAddress b) :
    exactFractionValue (outgoingSum edges source) = ratOutgoingSum edges source := by
  unfold outgoingSum
  rw [exactFractionValue_outgoingFold, exactFractionValue_zero, zero_add]

/-- Exact C007 ordered-pair sum has the recursive rational value above. -/
theorem exactFractionValue_orderedPairSum {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) :
    exactFractionValue (orderedPairSum edges source target) =
      ratOrderedPairSum edges source target := by
  unfold orderedPairSum
  rw [exactFractionValue_orderedPairFold, exactFractionValue_zero, zero_add]

/-- Rational C007 matrix-entry normal form. -/
def ratDirectedMatrixEntry {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) : ℚ :=
  if source = target then ratOutgoingSum edges source
  else -ratOrderedPairSum edges source target

/-- Exact value of the C007 source/out-degree entry. -/
theorem exactFractionValue_directedMatrixEntry {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) :
    exactFractionValue (directedMatrixEntry edges source target) =
      ratDirectedMatrixEntry edges source target := by
  by_cases hEqual : source = target
  · unfold directedMatrixEntry ratDirectedMatrixEntry
    rw [if_pos hEqual, if_pos hEqual, exactFractionValue_outgoingSum]
  · unfold directedMatrixEntry ratDirectedMatrixEntry
    rw [if_neg hEqual, if_neg hEqual, exactFractionValue_sub]
    rw [exactFractionValue_zero, exactFractionValue_orderedPairSum, zero_sub]

/-- Every rational ordered-pair sum is nonnegative. -/
theorem ratOrderedPairSum_nonnegative {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) :
    0 ≤ ratOrderedPairSum edges source target := by
  induction edges with
  | nil =>
      exact le_rfl
  | cons edge edges ih =>
      change
        0 ≤
          (if edge.source = source then
            if edge.target = target then edge.value else 0
          else 0) + ratOrderedPairSum edges source target
      by_cases hSource : edge.source = source
      · rw [if_pos hSource]
        by_cases hTarget : edge.target = target
        · rw [if_pos hTarget]
          exact add_nonneg (le_of_lt edge.positive) ih
        · rw [if_neg hTarget, zero_add]
          exact ih
      · rw [if_neg hSource, zero_add]
        exact ih

/-- A represented positive C005 ordered pair gives a strictly positive rational
ordered-pair sum. -/
theorem ratOrderedPairSum_pos_of_hasConductance {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b)
    (hConductance : HasConductance edges source target) :
    0 < ratOrderedPairSum edges source target := by
  induction edges with
  | nil =>
      obtain ⟨selected, hSelected, _hSource, _hTarget⟩ := hConductance
      cases hSelected
  | cons edge edges ih =>
      obtain ⟨selected, hSelected, hSource, hTarget⟩ := hConductance
      cases hSelected with
      | head =>
          cases hSource
          cases hTarget
          change
            0 <
              (if edge.source = edge.source then
                if edge.target = edge.target then edge.value else 0
              else 0) + ratOrderedPairSum edges edge.source edge.target
          rw [if_pos rfl, if_pos rfl]
          exact add_pos_of_pos_of_nonneg edge.positive
            (ratOrderedPairSum_nonnegative edges edge.source edge.target)
      | tail _ hTail =>
          have hTailConductance : HasConductance edges source target :=
            ⟨selected, hTail, hSource, hTarget⟩
          have hTailPositive : 0 < ratOrderedPairSum edges source target :=
            ih hTailConductance
          change
            0 <
              (if edge.source = source then
                if edge.target = target then edge.value else 0
              else 0) + ratOrderedPairSum edges source target
          by_cases hEdgeSource : edge.source = source
          · rw [if_pos hEdgeSource]
            by_cases hEdgeTarget : edge.target = target
            · rw [if_pos hEdgeTarget]
              exact add_pos_of_nonneg_of_pos (le_of_lt edge.positive) hTailPositive
            · rw [if_neg hEdgeTarget, zero_add]
              exact hTailPositive
          · rw [if_neg hEdgeSource, zero_add]
            exact hTailPositive

/-- No positive C005 edge contributes to an address-diagonal ordered-pair sum. -/
theorem ratOrderedPairSum_self_zero {b : BranchingParameter}
    (edges : List (DirectedConductance b)) (source : ProvenanceAddress b) :
    ratOrderedPairSum edges source source = 0 := by
  induction edges with
  | nil =>
      rfl
  | cons edge edges ih =>
      change
        (if edge.source = source then
          if edge.target = source then edge.value else 0
        else 0) + ratOrderedPairSum edges source source = 0
      by_cases hSource : edge.source = source
      · rw [if_pos hSource]
        have hTarget : edge.target ≠ source := by
          intro hEqual
          exact edge.distinct (hSource.trans hEqual.symm)
        rw [if_neg hTarget, zero_add, ih]
      · rw [if_neg hSource, zero_add, ih]

/-- One C005 edge contributes its value exactly once when target coordinates are
summed over the duplicate-free complete M001 cut. -/
theorem sum_single_edge_target_indicator {X : ResponseCapableState}
    (next : NextOpenSlot X) (edge : DirectedConductance X.grammar.branching)
    (hEdge : edge ∈ X.conductances)
    (source : ProvenanceAddress X.grammar.branching) :
    (∑ target,
      if edge.source = source then
        if edge.target = canonicalCutAddress next target then edge.value else 0
      else 0) =
      (if edge.source = source then edge.value else 0) := by
  by_cases hSource : edge.source = source
  · rw [if_pos hSource]
    obtain ⟨selected, hSelected⟩ := conductanceTargetCoordinate_exists next edge hEdge
    calc
      (∑ target,
        if edge.source = source then
          if edge.target = canonicalCutAddress next target then edge.value else 0
        else 0) =
          (∑ target,
            if edge.target = canonicalCutAddress next target then edge.value else 0) := by
        apply Finset.sum_congr rfl
        intro target _hTarget
        rw [if_pos hSource]
      _ = (if edge.target = canonicalCutAddress next selected then edge.value else 0) := by
        apply Fintype.sum_eq_single selected
        intro target hDistinct
        rw [if_neg]
        intro hTargetAddress
        apply hDistinct
        exact (canonicalCutAddress_injective next
          (hSelected.trans hTargetAddress)).symm
      _ = edge.value := by
        rw [if_pos hSelected.symm]
  · rw [if_neg hSource]
    apply Finset.sum_eq_zero
    intro target _hTarget
    rw [if_neg hSource]

/-- Summing all ordered-pair contributions over the complete M001 target order
recovers exactly the C007 outgoing sum. -/
theorem sum_ratOrderedPairSum_eq_ratOutgoingSum {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (edges : List (DirectedConductance X.grammar.branching))
    (hEndpoints : ∀ edge, edge ∈ edges →
      NodeBorn X.grammar X.bornNonRoot edge.target)
    (source : ProvenanceAddress X.grammar.branching) :
    (∑ target, ratOrderedPairSum edges source (canonicalCutAddress next target)) =
      ratOutgoingSum edges source := by
  induction edges with
  | nil =>
      apply Fintype.sum_eq_zero
      intro target
      rfl
  | cons edge edges ih =>
      have hEdgeBorn : NodeBorn X.grammar X.bornNonRoot edge.target :=
        hEndpoints edge (List.Mem.head edges)
      have hEdgeCoordinate :
          ∃ coordinate, canonicalCutAddress next coordinate = edge.target :=
        canonicalCutCoordinate_exists next (born_implies_carrier_mem hEdgeBorn)
      have hTailEndpoints : ∀ tailEdge, tailEdge ∈ edges →
          NodeBorn X.grammar X.bornNonRoot tailEdge.target := by
        intro tailEdge hTail
        exact hEndpoints tailEdge (List.Mem.tail edge hTail)
      have hIndicator :
          (∑ target,
            if edge.source = source then
              if edge.target = canonicalCutAddress next target then edge.value else 0
            else 0) =
            (if edge.source = source then edge.value else 0) := by
        by_cases hSource : edge.source = source
        · rw [if_pos hSource]
          obtain ⟨selected, hSelected⟩ := hEdgeCoordinate
          calc
            (∑ target,
              if edge.source = source then
                if edge.target = canonicalCutAddress next target then edge.value else 0
              else 0) =
                (∑ target,
                  if edge.target = canonicalCutAddress next target then edge.value else 0) := by
              apply Finset.sum_congr rfl
              intro target _hTarget
              rw [if_pos hSource]
            _ = (if edge.target = canonicalCutAddress next selected then edge.value else 0) := by
              apply Fintype.sum_eq_single selected
              intro target hDistinct
              rw [if_neg]
              intro hTargetAddress
              apply hDistinct
              exact (canonicalCutAddress_injective next
                (hSelected.trans hTargetAddress)).symm
            _ = edge.value := by
              rw [if_pos hSelected.symm]
        · rw [if_neg hSource]
          apply Finset.sum_eq_zero
          intro target _hTarget
          rw [if_neg hSource]
      change
        (∑ target,
          ((if edge.source = source then
              if edge.target = canonicalCutAddress next target then edge.value else 0
            else 0) +
            ratOrderedPairSum edges source (canonicalCutAddress next target))) =
          (if edge.source = source then edge.value else 0) +
            ratOutgoingSum edges source
      rw [Finset.sum_add_distrib, hIndicator, ih hTailEndpoints]

/-- Coordinate form of a rational C007 entry: one diagonal indicator minus the
full ordered-pair contribution. -/
theorem ratDirectedMatrixEntry_eq_indicator_sub_pair {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (edges : List (DirectedConductance X.grammar.branching))
    (source target : CutVertex (boundary next).length
      (CanonicalBirthLocalMeasurementCut.interior next).length) :
    ratDirectedMatrixEntry edges
        (canonicalCutAddress next source) (canonicalCutAddress next target) =
      (if target = source then
        ratOutgoingSum edges (canonicalCutAddress next source)
      else 0) -
        ratOrderedPairSum edges
          (canonicalCutAddress next source) (canonicalCutAddress next target) := by
  by_cases hCoordinate : target = source
  · cases hCoordinate
    unfold ratDirectedMatrixEntry
    rw [if_pos rfl, if_pos rfl, ratOrderedPairSum_self_zero, sub_zero]
  · have hAddress : canonicalCutAddress next source ≠ canonicalCutAddress next target := by
      intro hEqual
      apply hCoordinate
      exact (canonicalCutAddress_injective next hEqual).symm
    unfold ratDirectedMatrixEntry
    rw [if_neg hAddress, if_neg hCoordinate, zero_sub]

/-- The rational C007 source/out-degree row sums to zero on the complete ordered
M001 cut. -/
theorem ratDirectedMatrixEntry_row_sum_zero {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (source : CutVertex (boundary next).length
      (CanonicalBirthLocalMeasurementCut.interior next).length) :
    (∑ target,
      ratDirectedMatrixEntry X.conductances
        (canonicalCutAddress next source) (canonicalCutAddress next target)) = 0 := by
  have hEndpoints : ∀ edge, edge ∈ X.conductances →
      NodeBorn X.grammar X.bornNonRoot edge.target := by
    intro edge hEdge
    exact (X.conductanceEndpointsBorn edge hEdge).2
  have hDiagonal :
      (∑ target : CutVertex (boundary next).length
          (CanonicalBirthLocalMeasurementCut.interior next).length,
        if target = source then
          ratOutgoingSum X.conductances (canonicalCutAddress next source)
        else 0) =
        ratOutgoingSum X.conductances (canonicalCutAddress next source) := by
    calc
      (∑ target : CutVertex (boundary next).length
          (CanonicalBirthLocalMeasurementCut.interior next).length,
        if target = source then
          ratOutgoingSum X.conductances (canonicalCutAddress next source)
        else 0) =
          (if source = source then
            ratOutgoingSum X.conductances (canonicalCutAddress next source)
          else 0) := by
        apply Fintype.sum_eq_single source
        intro target hDistinct
        rw [if_neg hDistinct]
      _ = ratOutgoingSum X.conductances (canonicalCutAddress next source) := by
        rw [if_pos rfl]
  calc
    (∑ target,
      ratDirectedMatrixEntry X.conductances
        (canonicalCutAddress next source) (canonicalCutAddress next target)) =
        ∑ target,
          ((if target = source then
              ratOutgoingSum X.conductances (canonicalCutAddress next source)
            else 0) -
            ratOrderedPairSum X.conductances
              (canonicalCutAddress next source) (canonicalCutAddress next target)) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      exact ratDirectedMatrixEntry_eq_indicator_sub_pair
        next X.conductances source target
    _ =
        (∑ target,
          if target = source then
            ratOutgoingSum X.conductances (canonicalCutAddress next source)
          else 0) -
        (∑ target,
          ratOrderedPairSum X.conductances
            (canonicalCutAddress next source) (canonicalCutAddress next target)) := by
      rw [Finset.sum_sub_distrib]
    _ = 0 := by
      rw [hDiagonal]
      rw [sum_ratOrderedPairSum_eq_ratOutgoingSum next X.conductances
        hEndpoints (canonicalCutAddress next source)]
      exact sub_self _

/-- C007 block realization transfers each full-cut entry without changing its
exact rational value. -/
theorem blockEntry_eq_ratDirectedMatrixEntry {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (source target : CutVertex (boundary next).length
      (CanonicalBirthLocalMeasurementCut.interior next).length) :
    blockEntry realization.blocks source target =
      ratDirectedMatrixEntry X.conductances
        (canonicalCutAddress next source) (canonicalCutAddress next target) := by
  cases source with
  | inl sourceBoundary =>
      cases target with
      | inl targetBoundary =>
          have hRepresentation :=
            realization.realizes.1 sourceBoundary targetBoundary
          change realization.blocks.kBB sourceBoundary targetBoundary = _
          calc
            realization.blocks.kBB sourceBoundary targetBoundary =
                exactFractionValue
                  (directedMatrixEntry X.conductances
                    (boundaryAddress next sourceBoundary)
                    (boundaryAddress next targetBoundary)) :=
              (represents_iff_exactFractionValue_eq.mp hRepresentation).symm
            _ = _ := exactFractionValue_directedMatrixEntry _ _ _
      | inr targetInterior =>
          have hRepresentation :=
            realization.realizes.2.1 sourceBoundary targetInterior
          change realization.blocks.kBI sourceBoundary targetInterior = _
          calc
            realization.blocks.kBI sourceBoundary targetInterior =
                exactFractionValue
                  (directedMatrixEntry X.conductances
                    (boundaryAddress next sourceBoundary)
                    (interiorAddress next targetInterior)) :=
              (represents_iff_exactFractionValue_eq.mp hRepresentation).symm
            _ = _ := exactFractionValue_directedMatrixEntry _ _ _
  | inr sourceInterior =>
      cases target with
      | inl targetBoundary =>
          have hRepresentation :=
            realization.realizes.2.2.1 sourceInterior targetBoundary
          change realization.blocks.kIB sourceInterior targetBoundary = _
          calc
            realization.blocks.kIB sourceInterior targetBoundary =
                exactFractionValue
                  (directedMatrixEntry X.conductances
                    (interiorAddress next sourceInterior)
                    (boundaryAddress next targetBoundary)) :=
              (represents_iff_exactFractionValue_eq.mp hRepresentation).symm
            _ = _ := exactFractionValue_directedMatrixEntry _ _ _
      | inr targetInterior =>
          have hRepresentation :=
            realization.realizes.2.2.2 sourceInterior targetInterior
          change realization.blocks.kII sourceInterior targetInterior = _
          calc
            realization.blocks.kII sourceInterior targetInterior =
                exactFractionValue
                  (directedMatrixEntry X.conductances
                    (interiorAddress next sourceInterior)
                    (interiorAddress next targetInterior)) :=
              (represents_iff_exactFractionValue_eq.mp hRepresentation).symm
            _ = _ := exactFractionValue_directedMatrixEntry _ _ _

/-- Exact off-diagonal nonpositivity of every canonical C007 realization. -/
theorem canonicalBlocks_offDiagonalNonpositive {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    ∀ source target, source ≠ target →
      blockEntry realization.blocks source target ≤ 0 := by
  intro source target hDistinct
  have hAddress : canonicalCutAddress next source ≠ canonicalCutAddress next target := by
    intro hEqual
    exact hDistinct (canonicalCutAddress_injective next hEqual)
  rw [blockEntry_eq_ratDirectedMatrixEntry realization source target]
  unfold ratDirectedMatrixEntry
  rw [if_neg hAddress]
  exact neg_nonpos.mpr
    (ratOrderedPairSum_nonnegative X.conductances
      (canonicalCutAddress next source) (canonicalCutAddress next target))

/-- Exact full-row conservation of every canonical C007 realization. -/
theorem canonicalBlocks_rowConservative {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    ∀ source, ∑ target, blockEntry realization.blocks source target = 0 := by
  intro source
  calc
    (∑ target, blockEntry realization.blocks source target) =
        ∑ target,
          ratDirectedMatrixEntry X.conductances
            (canonicalCutAddress next source) (canonicalCutAddress next target) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      exact blockEntry_eq_ratDirectedMatrixEntry realization source target
    _ = 0 := ratDirectedMatrixEntry_row_sum_zero next source

/-- A C005 ordered conductance is a strictly positive arc of the corresponding
canonical C007 block realization. -/
theorem canonicalPositiveArc_of_hasConductance {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (source target : CutVertex (boundary next).length
      (CanonicalBirthLocalMeasurementCut.interior next).length)
    (hConductance : HasConductance X.conductances
      (canonicalCutAddress next source) (canonicalCutAddress next target)) :
    PositiveArc realization.blocks source target := by
  obtain ⟨edge, hEdge, hSource, hTarget⟩ := hConductance
  have hAddressDistinct :
      canonicalCutAddress next source ≠ canonicalCutAddress next target := by
    intro hEqual
    apply edge.distinct
    exact hSource.trans (hEqual.trans hTarget.symm)
  have hCoordinateDistinct : source ≠ target := by
    intro hEqual
    apply hAddressDistinct
    exact congrArg (canonicalCutAddress next) hEqual
  constructor
  · exact hCoordinateDistinct
  · rw [blockEntry_eq_ratDirectedMatrixEntry realization source target]
    unfold ratDirectedMatrixEntry
    rw [if_neg hAddressDistinct]
    exact neg_lt_zero.mpr
      (ratOrderedPairSum_pos_of_hasConductance X.conductances
        (canonicalCutAddress next source) (canonicalCutAddress next target)
        ⟨edge, hEdge, hSource, hTarget⟩)

end CNNAProofs.P001
