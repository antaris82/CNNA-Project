import Init.Data.List.Pairwise
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S01A_C005_ConductanceAppendClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S03A_C006_ExactFractionRatRealizationClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S04A_M001_PortSupportClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S10_M004_ResponseCoupledBirthLawBirthlawB

/-!
M004 live-update support closure for recurrent C005 realization.

M004 owns the exact support of the response-coupled relation delta.  T002 must
not re-prove that support.  This extension proves, for the already-defined M004
lift, that every new ordered pair touches the newborn, has born/newborn
endpoints, is non-reflexive, and that the complete ordered-pair list is unique.
The numerical ExactFraction-to-Rat bridge remains owned by C006.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open NextOpenProvenanceSlot
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open InterBirthDirectedResponse
open CanonicalResponseSteeringFunctionalSigmaBRnS

namespace ResponseCoupledBirthLawBirthlawB

/-- Ordered-pair distinction at M004 before rational C005 realization. -/
def DistinctRelationPair {b : BranchingParameter}
    (left right : DirectedRelationUpdate b) : Prop :=
  left.source ≠ right.source ∨ left.target ≠ right.target

/-- The relation-support part of one canonical M004 lift, in exactly the order
later appended by C008/C017. -/
def liveRelationDelta {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  parentChildUpdates next value ++
    ancestorBackreactionUpdates next value ++
    siblingBackreactionUpdates next value

/-- Strict ancestors remain already-born M001 ports. -/
theorem strictAncestorPort_born {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {a : ProvenanceAddress X.grammar.branching}
    (hPort : a ∈ strictAncestorPorts next) :
    NodeBorn X.grammar X.bornNonRoot a := by
  unfold strictAncestorPorts at hPort
  have hCausal : a ∈ causalPredecessorPorts next :=
    List.dropLast_subset (causalPredecessorPorts next) hPort
  exact causalPredecessorPort_born next hCausal

/-- The strict-ancestor list remains duplicate-free after dropping the parent. -/
theorem strictAncestorPorts_pairwise_ne {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    List.Pairwise (fun left right : ProvenanceAddress X.grammar.branching =>
      left ≠ right) (strictAncestorPorts next) := by
  unfold strictAncestorPorts
  have hSub := List.dropLast_sublist (causalPredecessorPorts next)
  have hNodup : (causalPredecessorPorts next).dropLast.Nodup :=
    hSub.nodup (causalPredecessorPorts_nodup next)
  exact (List.nodup_iff_pairwise_ne).1 hNodup

/-- Removing the last causal port removes the direct parent itself. -/
theorem parent_not_mem_strictAncestorPorts {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    parentAddress next ∉ strictAncestorPorts next := by
  obtain ⟨init, hCausal, hDrop⟩ :=
    causalPredecessorPorts_eq_strictPrefix_append_parent next
  unfold strictAncestorPorts
  rw [hDrop]
  have hNodup := causalPredecessorPorts_nodup next
  rw [hCausal] at hNodup
  have hParts := (List.nodup_append).1 hNodup
  intro hParent
  have hNe := hParts.2.2 (parentAddress next) hParent
    (parentAddress next) (List.mem_singleton.mpr rfl)
  exact hNe rfl

/-- Strict ancestors and earlier siblings are disjoint M001 roles. -/
theorem strictAncestorPort_ne_olderSiblingPort {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {ancestor sibling : ProvenanceAddress X.grammar.branching}
    (hAncestor : ancestor ∈ strictAncestorPorts next)
    (hSibling : sibling ∈ olderSiblingPorts next) :
    ancestor ≠ sibling := by
  unfold strictAncestorPorts at hAncestor
  have hCausal : ancestor ∈ causalPredecessorPorts next :=
    List.dropLast_subset (causalPredecessorPorts next) hAncestor
  exact causalPredecessorPort_ne_olderSiblingPort next hCausal hSibling

/-- Membership characterization of the two-orientation sibling recursion. -/
theorem siblingBackreactionAux_mem_cases {b : BranchingParameter}
    (child : ProvenanceAddress b) (siblings : List (ProvenanceAddress b))
    (value : ExactFraction) {update : DirectedRelationUpdate b}
    (hUpdate : update ∈ siblingBackreactionAux child siblings value) :
    ∃ sibling, sibling ∈ siblings ∧
      (update = directRelationUpdate sibling child value ∨
       update = directRelationUpdate child sibling value) := by
  induction siblings with
  | nil =>
      cases hUpdate
  | cons sibling rest ih =>
      change update ∈
        directRelationUpdate sibling child value ::
        directRelationUpdate child sibling value ::
        siblingBackreactionAux child rest value at hUpdate
      have hFirst := List.mem_cons.mp hUpdate
      cases hFirst with
      | inl hEq =>
          exact ⟨sibling, List.Mem.head rest, Or.inl hEq⟩
      | inr hTail =>
          have hSecond := List.mem_cons.mp hTail
          cases hSecond with
          | inl hEq =>
              exact ⟨sibling, List.Mem.head rest, Or.inr hEq⟩
          | inr hRest =>
              obtain ⟨other, hOther, hShape⟩ := ih hRest
              exact ⟨other, List.Mem.tail sibling hOther, hShape⟩

/-- The sibling recursion has no repeated ordered endpoint pair when the
sibling list itself is pairwise distinct and excludes the child. -/
theorem siblingBackreactionAux_pairwise_distinct {b : BranchingParameter}
    (child : ProvenanceAddress b) (siblings : List (ProvenanceAddress b))
    (value : ExactFraction)
    (hSiblings : List.Pairwise (fun left right : ProvenanceAddress b =>
      left ≠ right) siblings)
    (hChild : ∀ sibling, sibling ∈ siblings → child ≠ sibling) :
    List.Pairwise DistinctRelationPair
      (siblingBackreactionAux child siblings value) := by
  induction siblings with
  | nil =>
      exact List.Pairwise.nil
  | cons sibling rest ih =>
      change List.Pairwise DistinctRelationPair
        (directRelationUpdate sibling child value ::
         directRelationUpdate child sibling value ::
         siblingBackreactionAux child rest value)
      apply List.Pairwise.cons
      · intro update hUpdate
        have hCases := List.mem_cons.mp hUpdate
        cases hCases with
        | inl hOut =>
            rw [hOut]
            change sibling ≠ child ∨ child ≠ sibling
            exact Or.inl (Ne.symm (hChild sibling (List.Mem.head rest)))
        | inr hRecursive =>
            obtain ⟨other, hOther, hShape⟩ :=
              siblingBackreactionAux_mem_cases child rest value hRecursive
            have hSiblingOther : sibling ≠ other :=
              List.rel_of_pairwise_cons hSiblings hOther
            cases hShape with
            | inl hIncoming =>
                rw [hIncoming]
                change sibling ≠ other ∨ child ≠ child
                exact Or.inl hSiblingOther
            | inr hOutgoing =>
                rw [hOutgoing]
                change sibling ≠ child ∨ child ≠ other
                exact Or.inl (Ne.symm (hChild sibling (List.Mem.head rest)))
      · apply List.Pairwise.cons
        · intro update hUpdate
          obtain ⟨other, hOther, hShape⟩ :=
            siblingBackreactionAux_mem_cases child rest value hUpdate
          have hSiblingOther : sibling ≠ other :=
            List.rel_of_pairwise_cons hSiblings hOther
          cases hShape with
          | inl hIncoming =>
              rw [hIncoming]
              change child ≠ other ∨ sibling ≠ child
              exact Or.inr (Ne.symm (hChild sibling (List.Mem.head rest)))
          | inr hOutgoing =>
              rw [hOutgoing]
              change child ≠ child ∨ sibling ≠ other
              exact Or.inr hSiblingOther
        · apply ih
          · exact hSiblings.of_cons
          · intro other hOther
            exact hChild other (List.Mem.tail sibling hOther)

/-- Every relation in the M004 live delta carries exactly the supplied steering
fraction. -/
theorem liveRelationDelta_value_eq {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {update : DirectedRelationUpdate X.grammar.branching}
    (hUpdate : update ∈ liveRelationDelta next value) :
    update.value = value := by
  unfold liveRelationDelta at hUpdate
  have hOuter := List.mem_append.mp hUpdate
  cases hOuter with
  | inl hParentOrAncestor =>
      have hInner := List.mem_append.mp hParentOrAncestor
      cases hInner with
      | inl hParent =>
          unfold parentChildUpdates at hParent
          have hFirst := List.mem_cons.mp hParent
          cases hFirst with
          | inl hEq =>
              rw [hEq]
              rfl
          | inr hTail =>
              have hSecond := List.mem_cons.mp hTail
              cases hSecond with
              | inl hEq =>
                  rw [hEq]
                  rfl
              | inr hNil => cases hNil
      | inr hAncestor =>
          unfold ancestorBackreactionUpdates at hAncestor
          obtain ⟨ancestor, _hMem, hEq⟩ := List.mem_map.mp hAncestor
          rw [← hEq]
          rfl
  | inr hSibling =>
      unfold siblingBackreactionUpdates at hSibling
      obtain ⟨sibling, _hMem, hShape⟩ :=
        siblingBackreactionAux_mem_cases next.val (olderSiblingPorts next)
          value hSibling
      cases hShape with
      | inl hEq =>
          rw [hEq]
          rfl
      | inr hEq =>
          rw [hEq]
          rfl

/-- Every M004 live update touches the selected newborn in one orientation. -/
theorem liveRelationDelta_touches_child {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {update : DirectedRelationUpdate X.grammar.branching}
    (hUpdate : update ∈ liveRelationDelta next value) :
    update.source = next.val ∨ update.target = next.val := by
  unfold liveRelationDelta at hUpdate
  have hOuter := List.mem_append.mp hUpdate
  cases hOuter with
  | inl hParentOrAncestor =>
      have hInner := List.mem_append.mp hParentOrAncestor
      cases hInner with
      | inl hParent =>
          unfold parentChildUpdates at hParent
          have hFirst := List.mem_cons.mp hParent
          cases hFirst with
          | inl hEq =>
              rw [hEq]
              exact Or.inr rfl
          | inr hTail =>
              have hSecond := List.mem_cons.mp hTail
              cases hSecond with
              | inl hEq =>
                  rw [hEq]
                  exact Or.inl rfl
              | inr hNil => cases hNil
      | inr hAncestor =>
          unfold ancestorBackreactionUpdates at hAncestor
          obtain ⟨ancestor, _hMem, hEq⟩ := List.mem_map.mp hAncestor
          rw [← hEq]
          exact Or.inl rfl
  | inr hSibling =>
      unfold siblingBackreactionUpdates at hSibling
      obtain ⟨sibling, _hMem, hShape⟩ :=
        siblingBackreactionAux_mem_cases next.val (olderSiblingPorts next)
          value hSibling
      cases hShape with
      | inl hEq =>
          rw [hEq]
          exact Or.inr rfl
      | inr hEq =>
          rw [hEq]
          exact Or.inl rfl

/-- Every endpoint of the M004 live delta belongs to the successor carrier. -/
theorem liveRelationDelta_endpointsBorn {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {update : DirectedRelationUpdate X.grammar.branching}
    (hUpdate : update ∈ liveRelationDelta next value) :
    NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) update.source ∧
    NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) update.target := by
  have hChild : NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) next.val :=
    ResponseCapableState.nodeBorn_append_right (List.mem_singleton.mpr rfl)
  unfold liveRelationDelta at hUpdate
  have hOuter := List.mem_append.mp hUpdate
  cases hOuter with
  | inl hParentOrAncestor =>
      have hInner := List.mem_append.mp hParentOrAncestor
      cases hInner with
      | inl hParent =>
          have hParentBorn :
              NodeBorn X.grammar (X.bornNonRoot ++ [next.val])
                (parentAddress next) :=
            ResponseCapableState.nodeBorn_append_left (parent_born next)
          unfold parentChildUpdates at hParent
          have hFirst := List.mem_cons.mp hParent
          cases hFirst with
          | inl hEq =>
              rw [hEq]
              exact ⟨hParentBorn, hChild⟩
          | inr hTail =>
              have hSecond := List.mem_cons.mp hTail
              cases hSecond with
              | inl hEq =>
                  rw [hEq]
                  exact ⟨hChild, hParentBorn⟩
              | inr hNil => cases hNil
      | inr hAncestor =>
          unfold ancestorBackreactionUpdates at hAncestor
          obtain ⟨ancestor, hAncestorMem, hEq⟩ := List.mem_map.mp hAncestor
          have hAncestorBorn :
              NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) ancestor :=
            ResponseCapableState.nodeBorn_append_left
              (strictAncestorPort_born next hAncestorMem)
          rw [← hEq]
          exact ⟨hChild, hAncestorBorn⟩
  | inr hSibling =>
      unfold siblingBackreactionUpdates at hSibling
      obtain ⟨sibling, hSiblingMem, hShape⟩ :=
        siblingBackreactionAux_mem_cases next.val (olderSiblingPorts next)
          value hSibling
      have hSiblingBorn :
          NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) sibling :=
        ResponseCapableState.nodeBorn_append_left
          (olderSiblingPort_born next hSiblingMem)
      cases hShape with
      | inl hEq =>
          rw [hEq]
          exact ⟨hSiblingBorn, hChild⟩
      | inr hEq =>
          rw [hEq]
          exact ⟨hChild, hSiblingBorn⟩

/-- No canonical M004 live relation is a self-loop. -/
theorem liveRelationDelta_endpoints_distinct {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {update : DirectedRelationUpdate X.grammar.branching}
    (hUpdate : update ∈ liveRelationDelta next value) :
    update.source ≠ update.target := by
  unfold liveRelationDelta at hUpdate
  have hOuter := List.mem_append.mp hUpdate
  cases hOuter with
  | inl hParentOrAncestor =>
      have hInner := List.mem_append.mp hParentOrAncestor
      cases hInner with
      | inl hParent =>
          unfold parentChildUpdates at hParent
          have hFirst := List.mem_cons.mp hParent
          cases hFirst with
          | inl hEq =>
              rw [hEq]
              exact Ne.symm (child_ne_oldNodeBorn next (parent_born next))
          | inr hTail =>
              have hSecond := List.mem_cons.mp hTail
              cases hSecond with
              | inl hEq =>
                  rw [hEq]
                  exact child_ne_oldNodeBorn next (parent_born next)
              | inr hNil => cases hNil
      | inr hAncestor =>
          unfold ancestorBackreactionUpdates at hAncestor
          obtain ⟨ancestor, hAncestorMem, hEq⟩ := List.mem_map.mp hAncestor
          rw [← hEq]
          exact child_ne_oldNodeBorn next
            (strictAncestorPort_born next hAncestorMem)
  | inr hSibling =>
      unfold siblingBackreactionUpdates at hSibling
      obtain ⟨sibling, hSiblingMem, hShape⟩ :=
        siblingBackreactionAux_mem_cases next.val (olderSiblingPorts next)
          value hSibling
      have hChildSibling : next.val ≠ sibling :=
        child_ne_oldNodeBorn next (olderSiblingPort_born next hSiblingMem)
      cases hShape with
      | inl hEq =>
          rw [hEq]
          exact Ne.symm hChildSibling
      | inr hEq =>
          rw [hEq]
          exact hChildSibling

/-- The two direct parent/newborn relations are pairwise distinct. -/
theorem parentChildUpdates_pairwise_distinct {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    List.Pairwise DistinctRelationPair (parentChildUpdates next value) := by
  unfold parentChildUpdates
  apply List.Pairwise.cons
  · intro update hUpdate
    have hCases := List.mem_cons.mp hUpdate
    cases hCases with
    | inl hEq =>
        rw [hEq]
        change parentAddress next ≠ next.val ∨ next.val ≠ parentAddress next
        exact Or.inl (Ne.symm (child_ne_oldNodeBorn next (parent_born next)))
    | inr hNil => cases hNil
  · apply List.Pairwise.cons
    · intro update hUpdate
      cases hUpdate
    · exact List.Pairwise.nil

/-- Strict-ancestor updates have pairwise distinct targets. -/
theorem ancestorBackreactionUpdates_pairwise_distinct
    {X : ResponseCapableState} (next : NextOpenSlot X) (value : ExactFraction) :
    List.Pairwise DistinctRelationPair
      (ancestorBackreactionUpdates next value) := by
  unfold ancestorBackreactionUpdates
  apply (List.pairwise_map).2
  exact List.Pairwise.imp
    (fun hNe => by
      change next.val ≠ next.val ∨ _ ≠ _
      exact Or.inr hNe)
    (strictAncestorPorts_pairwise_ne next)

/-- Earlier-sibling updates are pairwise distinct ordered pairs. -/
theorem siblingBackreactionUpdates_pairwise_distinct
    {X : ResponseCapableState} (next : NextOpenSlot X) (value : ExactFraction) :
    List.Pairwise DistinctRelationPair
      (siblingBackreactionUpdates next value) := by
  unfold siblingBackreactionUpdates
  apply siblingBackreactionAux_pairwise_distinct
  · exact olderSiblingPorts_pairwise_ne next
  · intro sibling hSibling
    exact child_ne_oldNodeBorn next (olderSiblingPort_born next hSibling)

/-- Direct parent/child updates cannot duplicate strict-ancestor updates. -/
theorem parentChild_ne_ancestor_update {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {parentUpdate ancestorUpdate : DirectedRelationUpdate X.grammar.branching}
    (hParent : parentUpdate ∈ parentChildUpdates next value)
    (hAncestor : ancestorUpdate ∈ ancestorBackreactionUpdates next value) :
    DistinctRelationPair parentUpdate ancestorUpdate := by
  unfold ancestorBackreactionUpdates at hAncestor
  obtain ⟨ancestor, hAncestorMem, hAncestorEq⟩ := List.mem_map.mp hAncestor
  rw [← hAncestorEq]
  unfold parentChildUpdates at hParent
  have hFirst := List.mem_cons.mp hParent
  cases hFirst with
  | inl hEq =>
      rw [hEq]
      change parentAddress next ≠ next.val ∨ next.val ≠ ancestor
      exact Or.inl (Ne.symm (child_ne_oldNodeBorn next (parent_born next)))
  | inr hTail =>
      have hSecond := List.mem_cons.mp hTail
      cases hSecond with
      | inl hEq =>
          rw [hEq]
          change next.val ≠ next.val ∨ parentAddress next ≠ ancestor
          exact Or.inr (fun hParentEq =>
            parent_not_mem_strictAncestorPorts next (hParentEq ▸ hAncestorMem))
      | inr hNil => cases hNil

/-- Direct parent/child updates cannot duplicate sibling updates. -/
theorem parentChild_ne_sibling_update {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {parentUpdate siblingUpdate : DirectedRelationUpdate X.grammar.branching}
    (hParent : parentUpdate ∈ parentChildUpdates next value)
    (hSibling : siblingUpdate ∈ siblingBackreactionUpdates next value) :
    DistinctRelationPair parentUpdate siblingUpdate := by
  unfold siblingBackreactionUpdates at hSibling
  obtain ⟨sibling, hSiblingMem, hShape⟩ :=
    siblingBackreactionAux_mem_cases next.val (olderSiblingPorts next)
      value hSibling
  have hChildSibling : next.val ≠ sibling :=
    child_ne_oldNodeBorn next (olderSiblingPort_born next hSiblingMem)
  have hParentSibling : parentAddress next ≠ sibling := by
    intro hEq
    exact parent_not_mem_olderSiblingPorts next (hEq ▸ hSiblingMem)
  unfold parentChildUpdates at hParent
  have hFirst := List.mem_cons.mp hParent
  cases hFirst with
  | inl hParentEq =>
      rw [hParentEq]
      cases hShape with
      | inl hSiblingEq =>
          rw [hSiblingEq]
          change parentAddress next ≠ sibling ∨ next.val ≠ next.val
          exact Or.inl hParentSibling
      | inr hSiblingEq =>
          rw [hSiblingEq]
          change parentAddress next ≠ next.val ∨ next.val ≠ sibling
          exact Or.inl (Ne.symm (child_ne_oldNodeBorn next (parent_born next)))
  | inr hTail =>
      have hSecond := List.mem_cons.mp hTail
      cases hSecond with
      | inl hParentEq =>
          rw [hParentEq]
          cases hShape with
          | inl hSiblingEq =>
              rw [hSiblingEq]
              change next.val ≠ sibling ∨ parentAddress next ≠ next.val
              exact Or.inl hChildSibling
          | inr hSiblingEq =>
              rw [hSiblingEq]
              change next.val ≠ next.val ∨ parentAddress next ≠ sibling
              exact Or.inr hParentSibling
      | inr hNil => cases hNil

/-- Strict-ancestor updates cannot duplicate sibling updates. -/
theorem ancestor_ne_sibling_update {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    {ancestorUpdate siblingUpdate : DirectedRelationUpdate X.grammar.branching}
    (hAncestor : ancestorUpdate ∈ ancestorBackreactionUpdates next value)
    (hSibling : siblingUpdate ∈ siblingBackreactionUpdates next value) :
    DistinctRelationPair ancestorUpdate siblingUpdate := by
  unfold ancestorBackreactionUpdates at hAncestor
  obtain ⟨ancestor, hAncestorMem, hAncestorEq⟩ := List.mem_map.mp hAncestor
  rw [← hAncestorEq]
  unfold siblingBackreactionUpdates at hSibling
  obtain ⟨sibling, hSiblingMem, hShape⟩ :=
    siblingBackreactionAux_mem_cases next.val (olderSiblingPorts next)
      value hSibling
  have hChildSibling : next.val ≠ sibling :=
    child_ne_oldNodeBorn next (olderSiblingPort_born next hSiblingMem)
  have hAncestorSibling : ancestor ≠ sibling :=
    strictAncestorPort_ne_olderSiblingPort next hAncestorMem hSiblingMem
  cases hShape with
  | inl hEq =>
      rw [hEq]
      change next.val ≠ sibling ∨ ancestor ≠ next.val
      exact Or.inl hChildSibling
  | inr hEq =>
      rw [hEq]
      change next.val ≠ next.val ∨ ancestor ≠ sibling
      exact Or.inr hAncestorSibling

/-- The complete M004 live delta contains no duplicate ordered pair. -/
theorem liveRelationDelta_pairwise_distinct {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    List.Pairwise DistinctRelationPair (liveRelationDelta next value) := by
  unfold liveRelationDelta
  apply (List.pairwise_append).2
  constructor
  · apply (List.pairwise_append).2
    exact ⟨parentChildUpdates_pairwise_distinct next value,
      ancestorBackreactionUpdates_pairwise_distinct next value,
      fun _ hParent _ hAncestor =>
        parentChild_ne_ancestor_update next value hParent hAncestor⟩
  · constructor
    · exact siblingBackreactionUpdates_pairwise_distinct next value
    · intro left hLeft right hRight
      have hCases := List.mem_append.mp hLeft
      cases hCases with
      | inl hParent =>
          exact parentChild_ne_sibling_update next value hParent hRight
      | inr hAncestor =>
          exact ancestor_ne_sibling_update next value hAncestor hRight

/-- Both direct provenance-backbone orientations occur in the M004 live delta. -/
theorem parentBackbone_updates_mem_liveRelationDelta {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    directRelationUpdate (parentAddress next) next.val value ∈
        liveRelationDelta next value ∧
    directRelationUpdate next.val (parentAddress next) value ∈
        liveRelationDelta next value := by
  constructor
  · unfold liveRelationDelta parentChildUpdates
    exact (List.mem_append).2 (Or.inl
      ((List.mem_append).2 (Or.inl (List.Mem.head _))))
  · unfold liveRelationDelta parentChildUpdates
    exact (List.mem_append).2 (Or.inl
      ((List.mem_append).2 (Or.inl
        (List.Mem.tail _ (List.Mem.head _)))))

/-- In the active M004 domain every relation in the live delta carries a
strictly positive numerator.  This is an M004 value-support fact, not a T002
conversion assumption. -/
theorem liveRelationDelta_positiveNum {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ update, update ∈ liveRelationDelta next value → 0 < update.value.num := by
  intro update hUpdate
  rw [liveRelationDelta_value_eq next value hUpdate]
  exact hPositive

/-- Origin-local M004 support closure consumed by T002. -/
structure LiveRelationDeltaClosure {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) : Prop where
  valueEq : ∀ update, update ∈ liveRelationDelta next value →
    update.value = value
  endpointsBorn : ∀ update, update ∈ liveRelationDelta next value →
    NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) update.source ∧
    NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) update.target
  endpointsDistinct : ∀ update, update ∈ liveRelationDelta next value →
    update.source ≠ update.target
  touchesChild : ∀ update, update ∈ liveRelationDelta next value →
    update.source = next.val ∨ update.target = next.val
  pairsUnique : List.Pairwise DistinctRelationPair (liveRelationDelta next value)
  parentBackboneUpdates :
    directRelationUpdate (parentAddress next) next.val value ∈
        liveRelationDelta next value ∧
    directRelationUpdate next.val (parentAddress next) value ∈
        liveRelationDelta next value

/-- M004 proves its complete live-support closure for every exact steering value. -/
theorem liveRelationDeltaClosure {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    LiveRelationDeltaClosure next value := by
  exact {
    valueEq := fun _ h => liveRelationDelta_value_eq next value h
    endpointsBorn := fun _ h => liveRelationDelta_endpointsBorn next value h
    endpointsDistinct := fun _ h => liveRelationDelta_endpoints_distinct next value h
    touchesChild := fun _ h => liveRelationDelta_touches_child next value h
    pairsUnique := liveRelationDelta_pairwise_distinct next value
    parentBackboneUpdates := parentBackbone_updates_mem_liveRelationDelta next value }

/-- The relation fields of the canonical M004 birth law are exactly the
origin-owned live delta. -/
theorem birthLaw_live_fields_eq_delta {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value) :
    (birthLaw realization lambda value hPair hPositive).parentChildBirthUpdates ++
      (birthLaw realization lambda value hPair hPositive).ancestorBackreactionUpdates ++
      (birthLaw realization lambda value hPair hPositive).siblingBackreactionUpdates =
        liveRelationDelta next value := by
  rfl

end ResponseCoupledBirthLawBirthlawB

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
