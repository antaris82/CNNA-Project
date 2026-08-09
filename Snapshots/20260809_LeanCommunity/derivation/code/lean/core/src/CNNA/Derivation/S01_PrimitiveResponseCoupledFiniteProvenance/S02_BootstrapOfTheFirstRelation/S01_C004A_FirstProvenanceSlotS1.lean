import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule

/-!
Paper 1.2.1 / C004A — first provenance slot `s₁`.

C004A consumes C003 and the fixed C018 schedule convention.  The notation
`s₁` names the first combinatorial child position of the root in one-based
ordinal prose; its internal C003 sibling-rank label is zero, because the local
slot alphabet is `Fin b.value` and C018 orders siblings by increasing rank.

This module defines provenance only.  It introduces no spatial coordinate,
node id, event index, time, conductance, response, or birth dynamics.
The structural first slot exists even for cutoff `L = 0`; in that case its
one-step address lies outside the finite approximant.  The actual first
non-root birth is owned later by C013.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- C004A carries exactly its two direct predecessors, tied to one C003 grammar. -/
structure FirstProvenanceSlot where
  grammar : FiniteBAryProvenanceGrammar
  schedule : CanonicalBirthSchedule
  schedule_grammar : schedule.grammar = grammar

namespace FirstProvenanceSlot

/-- Construct C004A from the explicit C003 and C018 predecessors. -/
def fromPredecessors
    (grammar : FiniteBAryProvenanceGrammar)
    (schedule : CanonicalBirthSchedule)
    (h : schedule.grammar = grammar) : FirstProvenanceSlot where
  grammar := grammar
  schedule := schedule
  schedule_grammar := h

/-- Canonical constructor using the active C018 rule for the given C003 grammar. -/
def build (grammar : FiniteBAryProvenanceGrammar) : FirstProvenanceSlot where
  grammar := grammar
  schedule := CanonicalBirthSchedule.build grammar
  schedule_grammar := rfl

/-- The first local rank exists because I001 supplies `2 ≤ b`. -/
def firstRank (S : FirstProvenanceSlot) : ProvenanceSlot S.grammar.branching :=
  ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) S.grammar.branching.ge_two⟩

/-- The first provenance slot belongs to the root address. -/
def parentAddress (S : FirstProvenanceSlot) : ProvenanceAddress S.grammar.branching :=
  ProvenanceAddress.root S.grammar.branching

/-- Intrinsic one-step provenance address selected for `s₁`. -/
def address (S : FirstProvenanceSlot) : ProvenanceAddress S.grammar.branching :=
  ProvenanceAddress.snoc (parentAddress S) (firstRank S)

/-- `s₁` is first in prose but carries zero-based internal sibling rank `0`. -/
theorem firstRank_val (S : FirstProvenanceSlot) : (firstRank S).val = 0 :=
  rfl

/-- The parent of `s₁` is exactly the empty root address. -/
theorem parentAddress_root (S : FirstProvenanceSlot) :
    parentAddress S = ProvenanceAddress.root S.grammar.branching :=
  rfl

/-- The first slot address is exactly one C003 word extension of the root. -/
theorem address_eq_snoc (S : FirstProvenanceSlot) :
    address S = ProvenanceAddress.snoc (ProvenanceAddress.root S.grammar.branching) (firstRank S) :=
  rfl

/-- The first slot has intrinsic provenance depth exactly one. -/
theorem address_depth (S : FirstProvenanceSlot) :
    ProvenanceAddress.depth (address S) = 1 := by
  rw [address_eq_snoc, ProvenanceAddress.depth_snoc, ProvenanceAddress.depth_root]

/-- C003 recovers the root as the unique provenance parent of `s₁`. -/
theorem address_parent (S : FirstProvenanceSlot) :
    ProvenanceAddress.parent? (address S) = some (parentAddress S) := by
  change ProvenanceAddress.parent?
      (ProvenanceAddress.snoc
        (ProvenanceAddress.root S.grammar.branching)
        (firstRank S))
      = some (ProvenanceAddress.root S.grammar.branching)
  exact ProvenanceAddress.parent?_snoc
    (ProvenanceAddress.root S.grammar.branching)
    (firstRank S)

/-- C003 recovers rank zero as the final slot label of `s₁`. -/
theorem address_finalSlot (S : FirstProvenanceSlot) :
    ProvenanceAddress.finalSlot? (address S) = some (firstRank S) := by
  change ProvenanceAddress.finalSlot?
      (ProvenanceAddress.snoc
        (ProvenanceAddress.root S.grammar.branching)
        (firstRank S))
      = some (firstRank S)
  exact ProvenanceAddress.finalSlot?_snoc
    (ProvenanceAddress.root S.grammar.branching)
    (firstRank S)

/-- Rank zero is the least local slot under the C018 sibling order. -/
theorem firstRank_eq_or_before (S : FirstProvenanceSlot)
    (r : ProvenanceSlot S.grammar.branching) :
    r = firstRank S ∨ CanonicalBirthSchedule.SlotBefore (firstRank S) r := by
  cases Nat.eq_zero_or_pos r.val with
  | inl hZero =>
      apply Or.inl
      apply Fin.eq_of_val_eq
      exact hZero
  | inr hPos =>
      exact Or.inr hPos

/-- Thus C018 selects `s₁` before every distinct sibling slot of the root. -/
theorem address_before_distinct_root_sibling (S : FirstProvenanceSlot)
    (r : ProvenanceSlot S.grammar.branching)
    (hne : r ≠ firstRank S) :
    CanonicalBirthSchedule.BirthBefore
      (address S)
      (ProvenanceAddress.snoc (parentAddress S) r) := by
  cases firstRank_eq_or_before S r with
  | inl hEq =>
      exact False.elim (hne hEq)
  | inr hBefore =>
      exact CanonicalBirthSchedule.sameParentIncreasingRank
        (parentAddress S) (firstRank S) r hBefore

/-- The structural first slot is the minimum non-root provenance address under C018.
For every non-root address `c`, either `c` is `s₁` itself or `s₁` occurs before `c`. -/
theorem address_eq_or_before_nonroot (S : FirstProvenanceSlot)
    (c : ProvenanceAddress S.grammar.branching)
    (hnonroot : ProvenanceAddress.depth c ≠ 0) :
    c = address S ∨ CanonicalBirthSchedule.BirthBefore (address S) c := by
  cases c with
  | nil =>
      exact False.elim (hnonroot rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          cases firstRank_eq_or_before S x with
          | inl hEq =>
              apply Or.inl
              cases hEq
              rfl
          | inr hBefore =>
              apply Or.inr
              change CanonicalBirthSchedule.BirthBefore
                (ProvenanceAddress.snoc (parentAddress S) (firstRank S))
                (ProvenanceAddress.snoc (parentAddress S) x)
              exact CanonicalBirthSchedule.sameParentIncreasingRank
                (parentAddress S) (firstRank S) x hBefore
      | cons y ys =>
          apply Or.inr
          apply CanonicalBirthSchedule.shallower_before
          rw [address_depth]
          exact Nat.succ_lt_succ (Nat.zero_lt_succ ys.length)

/-- Therefore every distinct non-root provenance address occurs strictly after `s₁`. -/
theorem address_before_distinct_nonroot (S : FirstProvenanceSlot)
    (c : ProvenanceAddress S.grammar.branching)
    (hnonroot : ProvenanceAddress.depth c ≠ 0)
    (hne : c ≠ address S) :
    CanonicalBirthSchedule.BirthBefore (address S) c := by
  cases address_eq_or_before_nonroot S c hnonroot with
  | inl hEq =>
      exact False.elim (hne hEq)
  | inr hBefore =>
      exact hBefore

/-- Finite inclusion of `s₁` is exactly a cutoff question and is not a birth. -/
def WithinCutoff (S : FirstProvenanceSlot) : Prop :=
  ProvenanceAddress.depth (address S) ≤ S.grammar.cutoff.value

/-- Any cutoff with `1 ≤ L` contains the structural first-slot address. -/
theorem withinCutoff_of_one_le (S : FirstProvenanceSlot)
    (h : 1 ≤ S.grammar.cutoff.value) : WithinCutoff S := by
  unfold WithinCutoff
  rw [address_depth]
  exact h

/-- At cutoff `L = 0`, `s₁` remains structural but lies outside the finite cutoff. -/
theorem notWithinCutoff_at_zero (S : FirstProvenanceSlot)
    (hL : S.grammar.cutoff.value = 0) : ¬ WithinCutoff S := by
  intro hWithin
  unfold WithinCutoff at hWithin
  rw [address_depth, hL] at hWithin
  exact Nat.not_succ_le_zero 0 hWithin

end FirstProvenanceSlot

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
