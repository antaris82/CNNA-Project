import Init.Data.List.Pairwise
import Init.Data.List.FinRange
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S02A_C004_SuccessorBornPrefixClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S04_M001_CanonicalBirthLocalMeasurementCutCnSnplus1

/-!
M001 support closure needed by recurrent state closure.

These are facts about the provenance port lists created by M001 itself:
causal-prefix ports and earlier same-parent siblings are duplicate-free, and the
two roles are disjoint by provenance depth.  They are therefore proved here,
at the semantic origin of those lists, rather than inside T002.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open NextOpenProvenanceSlot

namespace CanonicalBirthLocalMeasurementCut

/-- Every element of a prefix chain is at least as deep as its starting prefix. -/
theorem prefixChainAux_depth_ge_pref {b : BranchingParameter}
    {pref rest a : ProvenanceAddress b}
    (h : a ∈ prefixChainAux pref rest) :
    ProvenanceAddress.depth pref ≤ ProvenanceAddress.depth a := by
  induction rest generalizing pref with
  | nil =>
      change a ∈ [pref] at h
      have hEq : a = pref := List.mem_singleton.mp h
      rw [hEq]
      exact Nat.le_refl _
  | cons localRank tail ih =>
      change a ∈ pref :: prefixChainAux (pref ++ [localRank]) tail at h
      have hCases := List.mem_cons.mp h
      cases hCases with
      | inl hEq =>
          rw [hEq]
          exact Nat.le_refl _
      | inr hTail =>
          have hDeep := ih hTail
          have hStep :
              ProvenanceAddress.depth pref + 1 =
                ProvenanceAddress.depth (pref ++ [localRank]) := by
            unfold ProvenanceAddress.depth
            rw [List.length_append, List.length_singleton]
          rw [← hStep] at hDeep
          exact Nat.le_trans (Nat.le_succ _) hDeep

/-- `prefixChainAux` ends in the complete final word. -/
theorem prefixChainAux_append_final {b : BranchingParameter}
    (pref rest : ProvenanceAddress b) :
    ∃ init,
      prefixChainAux pref rest = init ++ [pref ++ rest] := by
  induction rest generalizing pref with
  | nil =>
      refine ⟨[], ?_⟩
      change [pref] = [pref ++ []]
      rw [List.append_nil]
  | cons localRank tail ih =>
      obtain ⟨init, hInit⟩ := ih (pref ++ [localRank])
      refine ⟨pref :: init, ?_⟩
      change pref :: prefixChainAux (pref ++ [localRank]) tail =
        (pref :: init) ++ [pref ++ (localRank :: tail)]
      rw [hInit]
      have hFinal :
          (pref ++ [localRank]) ++ tail = pref ++ (localRank :: tail) := by
        exact List.append_assoc pref [localRank] tail
      rw [hFinal]
      rfl

private theorem dropLast_append_singleton {α : Type}
    (init : List α) (last : α) :
    (init ++ [last]).dropLast = init := by
  induction init with
  | nil =>
      rfl
  | cons head tail ih =>
      cases tail with
      | nil =>
          rfl
      | cons next rest =>
          change head :: ((next :: rest) ++ [last]).dropLast =
            head :: next :: rest
          rw [ih]

/-- The prefix chain itself is duplicate-free. -/
theorem prefixChainAux_nodup {b : BranchingParameter}
    (pref rest : ProvenanceAddress b) :
    (prefixChainAux pref rest).Nodup := by
  induction rest generalizing pref with
  | nil =>
      exact (List.nodup_iff_pairwise_ne).2 (List.pairwise_singleton _ pref)
  | cons localRank tail ih =>
      apply (List.nodup_cons).2
      constructor
      · intro hMem
        have hDeep := prefixChainAux_depth_ge_pref hMem
        have hStep :
            ProvenanceAddress.depth pref + 1 =
              ProvenanceAddress.depth (pref ++ [localRank]) := by
          unfold ProvenanceAddress.depth
          rw [List.length_append, List.length_singleton]
        rw [← hStep] at hDeep
        have hStrict : ProvenanceAddress.depth pref < ProvenanceAddress.depth pref :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hDeep
        exact (Nat.lt_irrefl _ hStrict)
      · exact ih (pref ++ [localRank])

/-- M001's root-to-parent causal port list has no duplicate address. -/
theorem causalPredecessorPorts_nodup {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    (causalPredecessorPorts next).Nodup := by
  unfold causalPredecessorPorts
  exact prefixChainAux_nodup [] (parentAddress next)

/-- The M001 causal list decomposes into strict ancestors followed by the
selected child's direct parent. -/
theorem causalPredecessorPorts_eq_strictPrefix_append_parent
    {X : ResponseCapableState} (next : NextOpenSlot X) :
    ∃ init,
      causalPredecessorPorts next = init ++ [parentAddress next] ∧
      (causalPredecessorPorts next).dropLast = init := by
  unfold causalPredecessorPorts
  obtain ⟨init, hInit⟩ := prefixChainAux_append_final
    ([] : ProvenanceAddress X.grammar.branching) (parentAddress next)
  have hFinal :
      ([] : ProvenanceAddress X.grammar.branching) ++ parentAddress next =
        parentAddress next := by
    rfl
  rw [hFinal] at hInit
  refine ⟨init, hInit, ?_⟩
  rw [hInit]
  exact dropLast_append_singleton init (parentAddress next)

/-- Every causal predecessor is no deeper than the direct parent. -/
theorem causalPredecessorPort_depth_le_parent {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {a : ProvenanceAddress X.grammar.branching}
    (hPort : a ∈ causalPredecessorPorts next) :
    ProvenanceAddress.depth a ≤ ProvenanceAddress.depth (parentAddress next) := by
  have hPrefix : List.IsPrefix a (parentAddress next) := by
    unfold causalPredecessorPorts at hPort
    have h := prefixChainAux_mem_prefix hPort
    change List.IsPrefix a (parentAddress next) at h
    exact h
  obtain ⟨suffix, hEq⟩ := hPrefix
  unfold ProvenanceAddress.depth
  have hLengths := congrArg List.length hEq
  rw [List.length_append] at hLengths
  exact Nat.le.intro hLengths

/-- Every earlier same-parent sibling has exactly the selected child's depth. -/
theorem olderSiblingPort_depth_eq_child {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {a : ProvenanceAddress X.grammar.branching}
    (hPort : a ∈ olderSiblingPorts next) :
    ProvenanceAddress.depth a = ProvenanceAddress.depth next.val := by
  unfold olderSiblingPorts at hPort
  obtain ⟨earlier, _hRange, hAddress⟩ := List.mem_map.mp hPort
  let localRank : ProvenanceSlot X.grammar.branching :=
    ⟨earlier.val, Nat.lt_trans earlier.isLt (rank next).isLt⟩
  have hAddress' :
      ProvenanceAddress.snoc (parentAddress next) localRank = a := hAddress
  rw [← hAddress', child_eq_snoc next,
    ProvenanceAddress.depth_snoc, ProvenanceAddress.depth_snoc]

/-- Core proof that the canonical finite enumeration contains no repeated `Fin`
index. -/
theorem finRange_pairwise_ne (n : Nat) :
    List.Pairwise (fun left right : Fin n => left ≠ right) (List.finRange n) := by
  induction n with
  | zero =>
      rw [List.finRange_zero]
      exact List.Pairwise.nil
  | succ n ih =>
      rw [List.finRange_succ]
      apply List.Pairwise.cons
      · intro later hLater
        obtain ⟨earlier, _hMem, hEq⟩ := List.mem_map.mp hLater
        rw [← hEq]
        intro hZero
        exact (Fin.succ_ne_zero earlier) hZero.symm
      · apply (List.pairwise_map).2
        exact List.Pairwise.imp
          (fun hNe hEq => hNe (Fin.succ_inj.mp hEq)) ih

/-- The earlier-sibling address list is duplicate-free. -/
theorem olderSiblingPorts_pairwise_ne {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    List.Pairwise (fun left right : ProvenanceAddress X.grammar.branching =>
      left ≠ right) (olderSiblingPorts next) := by
  unfold olderSiblingPorts
  apply (List.pairwise_map).2
  exact List.Pairwise.imp
    (fun hNe hAddress => by
      apply hNe
      apply Fin.ext
      have hSlot := ProvenanceAddress.snoc_slot_unique hAddress
      exact congrArg
        (fun slot : ProvenanceSlot X.grammar.branching => slot.val) hSlot)
    (finRange_pairwise_ne (rank next).val)

/-- M001's earlier-sibling list has no duplicate address. -/
theorem olderSiblingPorts_nodup {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    (olderSiblingPorts next).Nodup := by
  exact (List.nodup_iff_pairwise_ne).2 (olderSiblingPorts_pairwise_ne next)

/-- A causal predecessor and an earlier same-parent sibling can never be the
same provenance address: the sibling is one level deeper than the parent while
every causal port is at or above the parent. -/
theorem causalPredecessorPort_ne_olderSiblingPort {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {causal sibling : ProvenanceAddress X.grammar.branching}
    (hCausal : causal ∈ causalPredecessorPorts next)
    (hSibling : sibling ∈ olderSiblingPorts next) :
    causal ≠ sibling := by
  intro hEq
  have hCausalDepth := causalPredecessorPort_depth_le_parent next hCausal
  have hSiblingDepth := olderSiblingPort_depth_eq_child next hSibling
  have hChildDepth :
      ProvenanceAddress.depth next.val =
        ProvenanceAddress.depth (parentAddress next) + 1 := by
    rw [child_eq_snoc next, ProvenanceAddress.depth_snoc]
  rw [hEq, hSiblingDepth, hChildDepth] at hCausalDepth
  exact (Nat.not_succ_le_self _ hCausalDepth)

/-- The direct parent cannot be an earlier sibling. -/
theorem parent_not_mem_olderSiblingPorts {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    parentAddress next ∉ olderSiblingPorts next := by
  intro hSibling
  have hDepth := olderSiblingPort_depth_eq_child next hSibling
  have hChildDepth :
      ProvenanceAddress.depth next.val =
        ProvenanceAddress.depth (parentAddress next) + 1 := by
    rw [child_eq_snoc next, ProvenanceAddress.depth_snoc]
  rw [hChildDepth] at hDepth
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hDepth

/-- Complete M001 support package needed by M004/T002. -/
structure PortSupportClosure {X : ResponseCapableState}
    (next : NextOpenSlot X) : Prop where
  causalNodup : (causalPredecessorPorts next).Nodup
  siblingNodup : (olderSiblingPorts next).Nodup
  causalSiblingDisjoint :
    ∀ causal, causal ∈ causalPredecessorPorts next →
      ∀ sibling, sibling ∈ olderSiblingPorts next → causal ≠ sibling
  parentNotSibling : parentAddress next ∉ olderSiblingPorts next

/-- M001 proves all finite support-separation facts required by the M004 live
update. -/
theorem portSupportClosure {X : ResponseCapableState}
    (next : NextOpenSlot X) : PortSupportClosure next := by
  exact {
    causalNodup := causalPredecessorPorts_nodup next
    siblingNodup := olderSiblingPorts_nodup next
    causalSiblingDisjoint := fun _ hCausal _ hSibling =>
      causalPredecessorPort_ne_olderSiblingPort next hCausal hSibling
    parentNotSibling := parent_not_mem_olderSiblingPorts next }

end CanonicalBirthLocalMeasurementCut

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
