import Init.Data.List.Pairwise
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S02_C004_NextOpenProvenanceSlotSnplus1NGe1

/-!
C004 successor closure — the canonical next child extends the C005 born prefix.

These are order/cutoff facts about the selected provenance slot itself.  T002
consumes them but does not own them.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

namespace NextOpenProvenanceSlot

/-- Appending the C004 child preserves the finite cutoff predicate. -/
theorem born_snoc_withinCutoff {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    ∀ a, a ∈ X.bornNonRoot ++ [next.val] →
      ProvenanceAddress.depth a ≤ X.grammar.cutoff.value := by
  intro a ha
  have hCases := List.mem_append.mp ha
  cases hCases with
  | inl hOld =>
      exact X.bornWithinCutoff a hOld
  | inr hNew =>
      have hEq : a = next.val := List.mem_singleton.mp hNew
      rw [hEq]
      exact child_withinCutoff next

/-- Appending the C004 child preserves the non-root predicate. -/
theorem born_snoc_nonRootOnly {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    ∀ a, a ∈ X.bornNonRoot ++ [next.val] →
      ProvenanceAddress.depth a ≠ 0 := by
  intro a ha
  have hCases := List.mem_append.mp ha
  cases hCases with
  | inl hOld =>
      exact X.bornNonRootOnly a hOld
  | inr hNew =>
      have hEq : a = next.val := List.mem_singleton.mp hNew
      rw [hEq]
      exact child_nonroot next

/-- The C004 least-open child extends the C005 ordered prefix by one final
canonical element. -/
theorem born_snoc_ordered {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    List.Pairwise CanonicalBirthSchedule.BirthBefore
      (X.bornNonRoot ++ [next.val]) := by
  apply (List.pairwise_append).2
  refine ⟨X.bornOrdered, List.pairwise_singleton _ next.val, ?_⟩
  intro old hOld new hNew
  have hEq : new = next.val := List.mem_singleton.mp hNew
  rw [hEq]
  exact born_before_next next hOld

/-- The extended born list is still the complete admissible initial segment of
C018 up through the C004 child. -/
theorem born_snoc_initial {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    ∀ a c,
      c ∈ X.bornNonRoot ++ [next.val] →
      ProvenanceAddress.depth a ≠ 0 →
      ProvenanceAddress.depth a ≤ X.grammar.cutoff.value →
      CanonicalBirthSchedule.BirthBefore a c →
      a ∈ X.bornNonRoot ++ [next.val] := by
  intro a c hc hNonroot hCutoff hBefore
  have hCases := List.mem_append.mp hc
  cases hCases with
  | inl hOldC =>
      have hOldA := X.bornInitial a c hOldC hNonroot hCutoff hBefore
      exact (List.mem_append).2 (Or.inl hOldA)
  | inr hNewC =>
      have hEq : c = next.val := List.mem_singleton.mp hNewC
      rw [hEq] at hBefore
      have hOldA := earlier_admissible_is_born next a hNonroot hCutoff hBefore
      exact (List.mem_append).2 (Or.inl hOldA)

/-- The selected C004 child is distinct from every node already present in the
old C005 carrier, including the root. -/
theorem child_ne_oldNodeBorn {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {a : ProvenanceAddress X.grammar.branching}
    (hBorn : NodeBorn X.grammar X.bornNonRoot a) : next.val ≠ a := by
  intro hEq
  cases hBorn with
  | inl hRoot =>
      apply child_nonroot next
      rw [hEq, hRoot]
      rfl
  | inr hOld =>
      apply child_notBorn next
      rw [hEq]
      exact hOld

/-- The extended C004 prefix is nonempty independently of the old nonempty
witness. -/
theorem born_snoc_nonempty {X : ResponseCapableState}
    (next : NextOpenSlot X) : X.bornNonRoot ++ [next.val] ≠ [] := by
  intro hNil
  have hMem : next.val ∈ X.bornNonRoot ++ [next.val] :=
    (List.mem_append).2 (Or.inr (List.mem_singleton.mpr rfl))
  rw [hNil] at hMem
  cases hMem

/-- Origin-local bundle consumed by T002. -/
structure SuccessorBornPrefixClosure {X : ResponseCapableState}
    (next : NextOpenSlot X) : Prop where
  nonempty : X.bornNonRoot ++ [next.val] ≠ []
  withinCutoff : ∀ a, a ∈ X.bornNonRoot ++ [next.val] →
    ProvenanceAddress.depth a ≤ X.grammar.cutoff.value
  nonRootOnly : ∀ a, a ∈ X.bornNonRoot ++ [next.val] →
    ProvenanceAddress.depth a ≠ 0
  ordered : List.Pairwise CanonicalBirthSchedule.BirthBefore
    (X.bornNonRoot ++ [next.val])
  initial : ∀ a c,
    c ∈ X.bornNonRoot ++ [next.val] →
    ProvenanceAddress.depth a ≠ 0 →
    ProvenanceAddress.depth a ≤ X.grammar.cutoff.value →
    CanonicalBirthSchedule.BirthBefore a c →
    a ∈ X.bornNonRoot ++ [next.val]

/-- C004 proves the full born-prefix closure required downstream. -/
theorem successorBornPrefixClosure {X : ResponseCapableState}
    (next : NextOpenSlot X) : SuccessorBornPrefixClosure next := by
  exact {
    nonempty := born_snoc_nonempty next
    withinCutoff := born_snoc_withinCutoff next
    nonRootOnly := born_snoc_nonRootOnly next
    ordered := born_snoc_ordered next
    initial := born_snoc_initial next }

end NextOpenProvenanceSlot

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
