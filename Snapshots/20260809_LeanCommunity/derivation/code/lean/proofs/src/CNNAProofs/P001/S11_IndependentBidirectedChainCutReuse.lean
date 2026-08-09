import CNNAProofs.P001.S10_M003M004ProofFacades

/-!
# P001 R8 — independent bidirected-chain cut reuse

This module supplies the required second, genuinely independent cut family.
Unlike the canonical M001 birth cut, the family has no `ResponseCapableState`,
`NextOpenSlot`, provenance address, birth schedule, or C007 realization
parameter.  It is the two-boundary/one-interior bidirected chain

  left boundary  <->  interior  <->  right boundary

with strictly positive rational conductances `leftWeight` and `rightWeight`.
The four generic `DirectedCutHypotheses` are derived directly from its explicit
ordered Laplacian blocks.  The existing generic P001 theorem
`directedSchurDtnClosure` is then reused without duplicating any Schur/DtN,
maximum-principle, well-posedness, or response argument.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- Boundary conductance attached to the left (`0`) or right (`1`) port. -/
def independentChainBoundaryWeight
    (leftWeight rightWeight : ℚ) (index : Fin 2) : ℚ :=
  if index = 0 then leftWeight else rightWeight

/-- Explicit ordered Laplacian blocks for the independent bidirected chain.
The boundary order is left then right; the unique interior coordinate is last. -/
def independentBidirectedChainBlocks
    (leftWeight rightWeight : ℚ) : OrderedSchurBlocks 2 1 where
  boundaryNonempty := by omega
  kBB := fun row column =>
    if row = column then
      independentChainBoundaryWeight leftWeight rightWeight row
    else 0
  kBI := fun row _ =>
    -independentChainBoundaryWeight leftWeight rightWeight row
  kIB := fun _ column =>
    -independentChainBoundaryWeight leftWeight rightWeight column
  kII := fun _ _ => leftWeight + rightWeight

/-- Every off-diagonal entry of the independent chain is nonpositive. -/
theorem independentBidirectedChainOffDiagonalNonpositive
    (leftWeight rightWeight : ℚ)
    (hLeft : 0 < leftWeight)
    (hRight : 0 < rightWeight) :
    ∀ source target,
      source ≠ target →
        blockEntry (independentBidirectedChainBlocks leftWeight rightWeight)
          source target ≤ 0 := by
  intro source target hDistinct
  rcases source with source | source
  · rcases target with target | target
    · change
        (if source = target then
          independentChainBoundaryWeight leftWeight rightWeight source
        else 0) ≤ 0
      have hSourceTarget : source ≠ target := by
        intro hEqual
        exact hDistinct (congrArg Sum.inl hEqual)
      rw [if_neg hSourceTarget]
    · change -independentChainBoundaryWeight leftWeight rightWeight source ≤ 0
      fin_cases source
      · change -leftWeight ≤ 0
        linarith
      · change -rightWeight ≤ 0
        linarith
  · rcases target with target | target
    · change -independentChainBoundaryWeight leftWeight rightWeight target ≤ 0
      fin_cases target
      · change -leftWeight ≤ 0
        linarith
      · change -rightWeight ≤ 0
        linarith
    · have hEqual : source = target := Subsingleton.elim source target
      exact (hDistinct (congrArg Sum.inr hEqual)).elim

/-- Every row of the independent chain Laplacian sums exactly to zero. -/
theorem independentBidirectedChainRowConservative
    (leftWeight rightWeight : ℚ) :
    ∀ source,
      ∑ target,
        blockEntry (independentBidirectedChainBlocks leftWeight rightWeight)
          source target = 0 := by
  intro source
  rcases source with source | source
  · have hBoundary :
        (∑ target : Fin 2,
          if source = target then
            independentChainBoundaryWeight leftWeight rightWeight source
          else 0) =
          independentChainBoundaryWeight leftWeight rightWeight source := by
      fin_cases source
      · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        norm_num [independentChainBoundaryWeight]
      · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        norm_num [independentChainBoundaryWeight]
    have hInterior :
        (∑ _target : Fin 1,
          -independentChainBoundaryWeight leftWeight rightWeight source) =
          -independentChainBoundaryWeight leftWeight rightWeight source := by
      rw [Fin.sum_univ_succ]
      norm_num
    rw [Fintype.sum_sum_type]
    change
      (∑ target : Fin 2,
        if source = target then
          independentChainBoundaryWeight leftWeight rightWeight source
        else 0) +
      (∑ _target : Fin 1,
        -independentChainBoundaryWeight leftWeight rightWeight source) = 0
    rw [hBoundary, hInterior]
    ring
  · have hBoundary :
        (∑ target : Fin 2,
          -independentChainBoundaryWeight leftWeight rightWeight target) =
          -leftWeight + -rightWeight := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      norm_num [independentChainBoundaryWeight]
    have hInterior :
        (∑ _target : Fin 1, leftWeight + rightWeight) =
          leftWeight + rightWeight := by
      rw [Fin.sum_univ_succ]
      norm_num
    have hBoundaryBlock :
        (∑ target : Fin 2,
          blockEntry (independentBidirectedChainBlocks leftWeight rightWeight)
            (Sum.inr source) (Sum.inl target)) =
          (∑ target : Fin 2,
            -independentChainBoundaryWeight leftWeight rightWeight target) := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      rfl
    have hInteriorBlock :
        (∑ target : Fin 1,
          blockEntry (independentBidirectedChainBlocks leftWeight rightWeight)
            (Sum.inr source) (Sum.inr target)) =
          (∑ _target : Fin 1, leftWeight + rightWeight) := by
      calc
        (∑ target : Fin 1,
          blockEntry (independentBidirectedChainBlocks leftWeight rightWeight)
            (Sum.inr source) (Sum.inr target)) =
            blockEntry (independentBidirectedChainBlocks leftWeight rightWeight)
              (Sum.inr source) (Sum.inr (0 : Fin 1)) := by
                exact Fin.sum_univ_one _
        _ = leftWeight + rightWeight := by
              rfl
        _ = (∑ _target : Fin 1, leftWeight + rightWeight) := by
              exact hInterior.symm
    rw [Fintype.sum_sum_type, hBoundaryBlock, hInteriorBlock, hBoundary, hInterior]
    ring

/-- The unique interior vertex reaches the left boundary by its positive arc. -/
theorem independentBidirectedChainInteriorReachesBoundary
    (leftWeight rightWeight : ℚ)
    (hLeft : 0 < leftWeight) :
    ∀ interiorIndex : Fin 1,
      ∃ boundaryIndex : Fin 2,
        InteriorPathToBoundary
          (independentBidirectedChainBlocks leftWeight rightWeight)
          interiorIndex boundaryIndex := by
  intro interiorIndex
  have hInterior : interiorIndex = 0 := Subsingleton.elim interiorIndex 0
  cases hInterior
  refine ⟨0, InteriorPathToBoundary.direct ?_⟩
  refine ⟨?_, ?_⟩
  · intro hEqual
    cases hEqual
  · change -leftWeight < 0
    linarith

/-- The distinguished left port reaches the different right port through the
unique interior vertex. -/
theorem independentBidirectedChainDistinguishedReachesOtherBoundary
    (leftWeight rightWeight : ℚ)
    (hLeft : 0 < leftWeight)
    (hRight : 0 < rightWeight) :
    ∃ other : Fin 2,
      other ≠ (0 : Fin 2) ∧
        PositivePath
          (independentBidirectedChainBlocks leftWeight rightWeight)
          (Sum.inl (0 : Fin 2)) (Sum.inl other) := by
  refine ⟨1, by decide, ?_⟩
  refine PositivePath.tail
    (middle := Sum.inr (0 : Fin 1))
    ?_ ?_
  · apply PositivePath.edge
    refine ⟨?_, ?_⟩
    · intro hEqual
      cases hEqual
    · change -leftWeight < 0
      linarith
  · refine ⟨?_, ?_⟩
    · intro hEqual
      cases hEqual
    · change -rightWeight < 0
      linarith

/-- All four generic directed-cut hypotheses are derived for the independent
positive-weight chain family. -/
theorem independentBidirectedChainHypotheses
    (leftWeight rightWeight : ℚ)
    (hLeft : 0 < leftWeight)
    (hRight : 0 < rightWeight) :
    DirectedCutHypotheses
      (independentBidirectedChainBlocks leftWeight rightWeight) (0 : Fin 2) := by
  exact {
    offDiagonalNonpositive :=
      independentBidirectedChainOffDiagonalNonpositive
        leftWeight rightWeight hLeft hRight
    rowConservative :=
      independentBidirectedChainRowConservative leftWeight rightWeight
    everyInteriorReachesBoundary :=
      independentBidirectedChainInteriorReachesBoundary
        leftWeight rightWeight hLeft
    distinguishedReachesOtherBoundary :=
      independentBidirectedChainDistinguishedReachesOtherBoundary
        leftWeight rightWeight hLeft hRight }

/-- R8 reuse theorem: the already-proved generic P001 closure applies to the
independent bidirected-chain family. -/
theorem independentBidirectedChainClosure
    (leftWeight rightWeight : ℚ)
    (hLeft : 0 < leftWeight)
    (hRight : 0 < rightWeight) :
    DirectedSchurDtnClosure
      (independentBidirectedChainBlocks leftWeight rightWeight) (0 : Fin 2) := by
  exact directedSchurDtnClosure
    (independentBidirectedChainBlocks leftWeight rightWeight) (0 : Fin 2)
    (independentBidirectedChainHypotheses
      leftWeight rightWeight hLeft hRight)

/-- Public R8 contract: P001 is reused on a cut family whose carrier and
coordinates are independent of the canonical birth-local construction. -/
def SecondCutReuseContract : Prop :=
  ∀ leftWeight rightWeight : ℚ,
    0 < leftWeight →
    0 < rightWeight →
      DirectedSchurDtnClosure
        (independentBidirectedChainBlocks leftWeight rightWeight) (0 : Fin 2)

/-- R8 closes the second-cut reuse contract without adding a second copy of the
generic closure proof. -/
theorem secondCutReuseContract : SecondCutReuseContract := by
  intro leftWeight rightWeight hLeft hRight
  exact independentBidirectedChainClosure
    leftWeight rightWeight hLeft hRight

end CNNAProofs.P001
