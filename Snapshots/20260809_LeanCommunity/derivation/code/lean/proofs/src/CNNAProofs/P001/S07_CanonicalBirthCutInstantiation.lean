import CNNAProofs.P001.S06_DistinguishedPortStrictPositivity

/-!
# P001 R6 — canonical M001/C007/M003 birth-cut instantiation

This module performs only the cut-specific handoff from the generic P001
closure to the canonical recurrent birth cut.  It proves that the M001 boundary
has duplicate-free inherited coordinates, constructs the unique explicit parent
coordinate from the already-proved M003 membership theorem, identifies M003's
address-filtered parent aggregate with that single response diagonal, and
transports generic strict positivity to `PositiveSteering`.

No new graph hypothesis, inverse, regularizer, symmetrization, selected matrix
representative, or physical parameter is introduced.  The theorem consumes the
`DirectedCutHypotheses` object belonging to the concrete C007 realization; the
separate construction of that object from C005's positive parent backbone is
kept visible as the remaining state-to-cut structural obligation.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open NextOpenProvenanceSlot
open InterBirthDirectedResponse
open CanonicalResponseSteeringFunctionalSigmaBRnS

/-- C005's ordered non-root birth list contains no duplicate address. -/
theorem bornNonRoot_nodup (X : ResponseCapableState) : X.bornNonRoot.Nodup := by
  letI : Std.Irrefl
      (@CanonicalBirthSchedule.BirthBefore X.grammar.branching) :=
    ⟨fun address =>
      CanonicalBirthSchedule.birthBefore_irrefl
        (b := X.grammar.branching) address⟩
  exact X.bornOrdered.nodup

/-- The root cannot occur in C005's explicitly non-root birth list. -/
theorem root_not_mem_bornNonRoot (X : ResponseCapableState) :
    ResponseCapableState.rootAddress X ∉ X.bornNonRoot := by
  intro hRoot
  have hDepth := X.bornNonRootOnly (ResponseCapableState.rootAddress X) hRoot
  unfold ResponseCapableState.rootAddress at hDepth
  rw [ProvenanceAddress.depth_root] at hDepth
  exact hDepth rfl

/-- The complete M001 carrier inherits duplicate-freeness from C005/C018. -/
theorem canonicalCarrier_nodup (X : ResponseCapableState) :
    (canonicalCarrier X).Nodup := by
  unfold canonicalCarrier
  exact List.Nodup.cons (root_not_mem_bornNonRoot X) (bornNonRoot_nodup X)

/-- Filtering the duplicate-free carrier preserves duplicate-freeness of the
canonical M001 boundary order. -/
theorem boundary_nodup {X : ResponseCapableState} (next : NextOpenSlot X) :
    (boundary next).Nodup := by
  unfold boundary
  exact (canonicalCarrier_nodup X).filter (portFlag next)

/-- The complementary M001 interior order is duplicate-free as well. -/
theorem interior_nodup {X : ResponseCapableState} (next : NextOpenSlot X) :
    (CanonicalBirthLocalMeasurementCut.interior next).Nodup := by
  unfold CanonicalBirthLocalMeasurementCut.interior
  exact (canonicalCarrier_nodup X).filter (fun address => !(portFlag next address))

/-- Membership of the slot parent in M001 yields an explicit parent coordinate;
no choice is retained in the public result. -/
theorem distinguishedParentIndex_exists {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    ∃ index : Fin (boundary next).length,
      boundaryAddress next index = parentAddress next := by
  change ∃ index : Fin (boundary next).length,
    (boundary next).get index = parentAddress next
  exact List.get_of_mem (parent_mem_boundary next)

/-- Positive rational value of a positive-denominator exact fraction forces its
stored numerator to be strictly positive. -/
theorem positiveSteering_of_exactFractionValue_pos (value : BirthLocalSchurDtnPrimitive.ExactFraction)
    (hPositive : 0 < exactFractionValue value) : PositiveSteering value := by
  unfold PositiveSteering
  have hDenInt : 0 < Int.ofNat value.den :=
    (Int.natCast_pos).2 value.denPos
  have hValueNonnegative : 0 ≤ exactFractionValue value := le_of_lt hPositive
  have hNumeratorNonnegative : 0 ≤ value.num := by
    unfold exactFractionValue at hValueNonnegative
    rw [← Rat.divInt_ofNat] at hValueNonnegative
    exact (Rat.divInt_nonneg_iff_of_pos_right hDenInt).mp hValueNonnegative
  have hNumeratorNonzero : value.num ≠ 0 := by
    have hValueNonzero : exactFractionValue value ≠ 0 := ne_of_gt hPositive
    unfold exactFractionValue at hValueNonzero
    exact (Rat.mkRat_ne_zero (Nat.ne_of_gt value.denPos)).mp hValueNonzero
  exact lt_of_le_of_ne hNumeratorNonnegative (Ne.symm hNumeratorNonzero)

/-- In a duplicate-free M001 boundary, the address-filtered M003 parent sum is
exactly the single diagonal selected by the explicit parent coordinate. -/
theorem parentSelfResponse_value_eq_parentDiagonal
    {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (parent : DistinguishedParentIndex next)
    (response : BirthLocalSchurDtnPrimitive.ExactFractionMatrix
      (boundary next).length (boundary next).length) :
    exactFractionValue (parentSelfResponse next response) =
      exactFractionValue (response parent.index parent.index) := by
  unfold parentSelfResponse
  rw [exactFractionValue_finFoldl_add]
  rw [exactFractionValue_zero]
  rw [finFoldl_add_eq_sum]
  have hSingle :
      (∑ index : Fin (boundary next).length,
          exactFractionValue (parentDiagonalTerm next response index)) =
        exactFractionValue
          (parentDiagonalTerm next response parent.index) := by
    apply Finset.sum_eq_single parent.index
    · intro index _hIndex hDistinct
      have hAddressDistinct :
          boundaryAddress next index ≠ parentAddress next := by
        intro hAddress
        apply hDistinct
        apply (boundary_nodup next).injective_get
        -- The goal already has the exact get-equality required by injective_get.
        exact hAddress.trans parent.address_eq_parent.symm
      unfold parentDiagonalTerm
      rw [if_neg hAddressDistinct]
      exact exactFractionValue_zero
    · intro hNotMember
      exact False.elim (hNotMember (Finset.mem_univ parent.index))
  rw [hSingle]
  unfold parentDiagonalTerm
  rw [if_pos parent.address_eq_parent]

/-- The generic strict parent diagonal implies the exact M003 positivity
predicate for every response/steering representative pair. -/
theorem m003ParentPositivity_of_genericClosure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (parent : DistinguishedParentIndex next)
    (closure : DirectedSchurDtnClosure realization.blocks parent.index) :
    DirectedKronParentPositivityAt realization := by
  intro response value hPair
  have hParentDiagonal :
      0 < exactFractionValue (response parent.index parent.index) :=
    closure.distinguishedPortPositive response hPair.1
  have hAggregate :
      exactFractionValue (parentSelfResponse next response) =
        exactFractionValue (response parent.index parent.index) :=
    parentSelfResponse_value_eq_parentDiagonal next parent response
  have hSigma :
      exactFractionValue (sigma next response) =
        exactFractionValue (response parent.index parent.index) := by
    rw [sigma_eq_parentSelfResponse]
    exact hAggregate
  have hValue :
      exactFractionValue value = exactFractionValue (sigma next response) :=
    sameValue_iff_exactFractionValue_eq.mp hPair.2
  apply positiveSteering_of_exactFractionValue_pos value
  rw [hValue, hSigma]
  exact hParentDiagonal

/-- R6 canonical handoff for one actual C007 realization and its explicit M001
parent coordinate. -/
theorem canonicalBirthCutClosure_of_hypotheses
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (parent : DistinguishedParentIndex next)
    (hypotheses : DirectedCutHypotheses realization.blocks parent.index) :
    CanonicalBirthCutClosure realization parent := by
  have hGeneric : DirectedSchurDtnClosure realization.blocks parent.index :=
    directedSchurDtnClosure realization.blocks parent.index hypotheses
  exact {
    genericClosure := hGeneric
    c007ResponseDomain := hGeneric.c006InteriorAdmissible
    m003ParentPositivity :=
      m003ParentPositivity_of_genericClosure realization parent hGeneric }

/-- The public canonical-instantiation contract is inhabited without duplicating
any generic Schur/DtN proof inside M003. -/
theorem canonicalBirthCutClosureContract : CanonicalBirthCutClosureContract := by
  intro X next realization parent hypotheses
  exact canonicalBirthCutClosure_of_hypotheses realization parent hypotheses

end CNNAProofs.P001
