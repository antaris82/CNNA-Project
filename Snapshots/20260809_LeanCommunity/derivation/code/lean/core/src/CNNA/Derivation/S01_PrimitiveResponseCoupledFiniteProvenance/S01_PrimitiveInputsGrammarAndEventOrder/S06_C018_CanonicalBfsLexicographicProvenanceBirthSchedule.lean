import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S05_C003_FiniteBAryProvenanceGrammar

/-!
Paper 1.1.6 / C018 — canonical BFS/lexicographic provenance birth schedule.

C018 consumes only the C003 finite b-ary provenance grammar.  It fixes the
active construction convention extensionally:

* smaller provenance depth is earlier (breadth first);
* at equal depth, provenance words are ordered lexicographically by slot value;
* children of one parent are therefore ordered by increasing sibling rank;
* the active rule is slot-step, not layer-batch.

The root is already present from C002/C003 and is not a new open birth slot.
This module owns only order.  It does not assign event indices, response-derived
time, node ids, conductance, response, geometry, or dynamics.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

namespace CanonicalBirthSchedule

/-- Local rank comparison used by the canonical schedule. -/
def SlotBefore {b : BranchingParameter} (r s : ProvenanceSlot b) : Prop :=
  r.val < s.val

/-- Lexicographic comparison of provenance words at a fixed depth. -/
def AddressLexBefore {b : BranchingParameter}
    (a c : ProvenanceAddress b) : Prop :=
  List.Lex SlotBefore a c

/-- Breadth-first, then lexicographic strict order on provenance addresses. -/
def BirthBefore {b : BranchingParameter}
    (a c : ProvenanceAddress b) : Prop :=
  ProvenanceAddress.depth a < ProvenanceAddress.depth c ∨
    (ProvenanceAddress.depth a = ProvenanceAddress.depth c ∧
      AddressLexBefore a c)

/-- A strictly shallower address is always earlier. -/
theorem shallower_before {b : BranchingParameter}
    {a c : ProvenanceAddress b}
    (h : ProvenanceAddress.depth a < ProvenanceAddress.depth c) :
    BirthBefore a c :=
  Or.inl h

/-- At equal depth, lexicographic address order determines the schedule. -/
theorem sameDepthLex_before {b : BranchingParameter}
    {a c : ProvenanceAddress b}
    (hDepth : ProvenanceAddress.depth a = ProvenanceAddress.depth c)
    (hLex : AddressLexBefore a c) : BirthBefore a c :=
  Or.inr ⟨hDepth, hLex⟩

/-- Appending different final ranks to one parent preserves increasing-rank order. -/
theorem lex_snoc_same_parent {b : BranchingParameter}
    (u : ProvenanceAddress b) (r s : ProvenanceSlot b)
    (h : SlotBefore r s) :
    AddressLexBefore (ProvenanceAddress.snoc u r) (ProvenanceAddress.snoc u s) := by
  induction u with
  | nil =>
      exact List.Lex.rel h
  | cons x xs ih =>
      exact List.Lex.cons ih

/-- Children of one parent occur in increasing sibling-rank order. -/
theorem sameParentIncreasingRank {b : BranchingParameter}
    (u : ProvenanceAddress b) (r s : ProvenanceSlot b)
    (h : SlotBefore r s) :
    BirthBefore (ProvenanceAddress.snoc u r) (ProvenanceAddress.snoc u s) := by
  apply sameDepthLex_before
  · rw [ProvenanceAddress.depth_snoc, ProvenanceAddress.depth_snoc]
  · exact lex_snoc_same_parent u r s h

/-- Every parent address precedes each of its children by breadth-first depth. -/
theorem parent_before_child {b : BranchingParameter}
    (u : ProvenanceAddress b) (r : ProvenanceSlot b) :
    BirthBefore u (ProvenanceAddress.snoc u r) := by
  apply shallower_before
  rw [ProvenanceAddress.depth_snoc]
  exact Nat.lt_succ_self (ProvenanceAddress.depth u)

/-- The local rank comparison is irreflexive. -/
theorem slotBefore_irrefl {b : BranchingParameter} (r : ProvenanceSlot b) :
    ¬ SlotBefore r r :=
  Nat.lt_irrefl r.val

/-- Lexicographic address comparison is irreflexive for the local rank order. -/
theorem addressLexBefore_irrefl {b : BranchingParameter} :
    ∀ a : ProvenanceAddress b, ¬ AddressLexBefore a a
  | [] => by
      intro h
      cases h
  | x :: xs => by
      intro h
      cases h with
      | rel hr =>
          exact Nat.lt_irrefl x.val hr
      | cons ht =>
          exact addressLexBefore_irrefl xs ht

/-- Lexicographic address comparison is transitive. -/
theorem addressLexBefore_trans {b : BranchingParameter} :
    ∀ {a c e : ProvenanceAddress b},
      AddressLexBefore a c → AddressLexBefore c e → AddressLexBefore a e := by
  intro a
  induction a with
  | nil =>
      intro c e h1 h2
      cases c with
      | nil =>
          cases h1
      | cons y ys =>
          cases e with
          | nil =>
              cases h2
          | cons z zs =>
              exact List.Lex.nil
  | cons x xs ih =>
      intro c e h1 h2
      cases c with
      | nil =>
          cases h1
      | cons y ys =>
          cases e with
          | nil =>
              cases h2
          | cons z zs =>
              cases h1 with
              | rel hxy =>
                  cases h2 with
                  | rel hyz =>
                      exact List.Lex.rel (Nat.lt_trans hxy hyz)
                  | cons _ =>
                      exact List.Lex.rel hxy
              | cons ht1 =>
                  cases h2 with
                  | rel hyz =>
                      exact List.Lex.rel hyz
                  | cons ht2 =>
                      exact List.Lex.cons (ih ht1 ht2)

/-- Lexicographic comparison on provenance words is constructively trichotomous. -/
theorem addressLexBefore_trichotomy {b : BranchingParameter} :
    ∀ a c : ProvenanceAddress b,
      AddressLexBefore a c ∨ a = c ∨ AddressLexBefore c a
  | [], [] =>
      Or.inr (Or.inl rfl)
  | [], _ :: _ =>
      Or.inl List.Lex.nil
  | _ :: _, [] =>
      Or.inr (Or.inr List.Lex.nil)
  | x :: xs, y :: ys => by
      cases Nat.lt_trichotomy x.val y.val with
      | inl hxy =>
          exact Or.inl (List.Lex.rel hxy)
      | inr hrest =>
          cases hrest with
          | inl hEq =>
              have hxy : x = y := Fin.eq_of_val_eq hEq
              cases hxy
              cases addressLexBefore_trichotomy xs ys with
              | inl hlt =>
                  exact Or.inl (List.Lex.cons hlt)
              | inr htail =>
                  cases htail with
                  | inl hTailEq =>
                      exact Or.inr (Or.inl (congrArg (fun t => x :: t) hTailEq))
                  | inr hgt =>
                      exact Or.inr (Or.inr (List.Lex.cons hgt))
          | inr hyx =>
              exact Or.inr (Or.inr (List.Lex.rel hyx))

/-- The canonical birth order is strict: no address precedes itself. -/
theorem birthBefore_irrefl {b : BranchingParameter} (a : ProvenanceAddress b) :
    ¬ BirthBefore a a := by
  intro h
  cases h with
  | inl hDepth =>
      exact Nat.lt_irrefl (ProvenanceAddress.depth a) hDepth
  | inr hRest =>
      exact addressLexBefore_irrefl a hRest.2

/-- The canonical birth order is transitive. -/
theorem birthBefore_trans {b : BranchingParameter} {a c e : ProvenanceAddress b}
    (h1 : BirthBefore a c) (h2 : BirthBefore c e) : BirthBefore a e := by
  cases h1 with
  | inl d1 =>
      cases h2 with
      | inl d2 =>
          exact Or.inl (Nat.lt_trans d1 d2)
      | inr d2 =>
          exact Or.inl (d2.1 ▸ d1)
  | inr d1 =>
      cases h2 with
      | inl d2 =>
          exact Or.inl (d1.1 ▸ d2)
      | inr d2 =>
          exact Or.inr ⟨d1.1.trans d2.1, addressLexBefore_trans d1.2 d2.2⟩

/-- The canonical birth order is asymmetric. -/
theorem birthBefore_asymm {b : BranchingParameter} {a c : ProvenanceAddress b}
    (h1 : BirthBefore a c) (h2 : BirthBefore c a) : False :=
  birthBefore_irrefl a (birthBefore_trans h1 h2)

/-- The canonical birth order is constructively trichotomous. -/
theorem birthBefore_trichotomy {b : BranchingParameter} (a c : ProvenanceAddress b) :
    BirthBefore a c ∨ a = c ∨ BirthBefore c a := by
  cases Nat.lt_trichotomy (ProvenanceAddress.depth a) (ProvenanceAddress.depth c) with
  | inl hDepth =>
      exact Or.inl (Or.inl hDepth)
  | inr hrest =>
      cases hrest with
      | inl hDepthEq =>
          cases addressLexBefore_trichotomy a c with
          | inl hLex =>
              exact Or.inl (Or.inr ⟨hDepthEq, hLex⟩)
          | inr hAddrRest =>
              cases hAddrRest with
              | inl hAddrEq =>
                  exact Or.inr (Or.inl hAddrEq)
              | inr hLexRev =>
                  exact Or.inr (Or.inr (Or.inr ⟨hDepthEq.symm, hLexRev⟩))
      | inr hDepthRev =>
          exact Or.inr (Or.inr (Or.inl hDepthRev))

/-- Distinct addresses are comparable in exactly one schedule direction. -/
theorem birthBefore_total_of_ne {b : BranchingParameter} {a c : ProvenanceAddress b}
    (hne : a ≠ c) : BirthBefore a c ∨ BirthBefore c a := by
  cases birthBefore_trichotomy a c with
  | inl hBefore =>
      exact Or.inl hBefore
  | inr hrest =>
      cases hrest with
      | inl hEq =>
          exact False.elim (hne hEq)
      | inr hAfter =>
          exact Or.inr hAfter

end CanonicalBirthSchedule

/-- C018 carries only its sole direct scientific predecessor C003. -/
structure CanonicalBirthSchedule where
  grammar : FiniteBAryProvenanceGrammar

namespace CanonicalBirthSchedule

/-- Canonical constructor from the already-derived C003 grammar. -/
def build (grammar : FiniteBAryProvenanceGrammar) : CanonicalBirthSchedule where
  grammar := grammar

/-- Constructor equation exposing the sole C003 predecessor. -/
theorem build_grammar (grammar : FiniteBAryProvenanceGrammar) :
    (build grammar).grammar = grammar :=
  rfl

/-- An admissible open birth slot is a bounded parent, a local rank, and the
proof that the resulting child remains inside the C003 cutoff. -/
structure OpenBirthSlot (S : CanonicalBirthSchedule) where
  parent : BoundedProvenanceAddress S.grammar.branching S.grammar.cutoff
  rank : ProvenanceSlot S.grammar.branching
  childDepthWithinCutoff :
    Nat.succ (ProvenanceAddress.depth parent.address) ≤ S.grammar.cutoff.value

namespace OpenBirthSlot

/-- The child address selected by one open slot. -/
def childAddress {S : CanonicalBirthSchedule} (slot : OpenBirthSlot S) :
    BoundedProvenanceAddress S.grammar.branching S.grammar.cutoff :=
  BoundedProvenanceAddress.child
    slot.parent slot.rank slot.childDepthWithinCutoff

/-- Child formation is exactly C003 word extension. -/
theorem childAddress_address {S : CanonicalBirthSchedule} (slot : OpenBirthSlot S) :
    (childAddress slot).address =
      ProvenanceAddress.snoc slot.parent.address slot.rank :=
  rfl

end OpenBirthSlot

/-- Extensional order on open slots induced by their selected child addresses. -/
def OpenSlotBefore {S : CanonicalBirthSchedule}
    (left right : OpenBirthSlot S) : Prop :=
  BirthBefore
    (OpenBirthSlot.childAddress left).address
    (OpenBirthSlot.childAddress right).address

/-- For the same bounded parent, a smaller rank gives the earlier open slot. -/
theorem sameParentOpenSlotIncreasingRank {S : CanonicalBirthSchedule}
    (parent : BoundedProvenanceAddress S.grammar.branching S.grammar.cutoff)
    (r s : ProvenanceSlot S.grammar.branching)
    (hr : Nat.succ (ProvenanceAddress.depth parent.address) ≤ S.grammar.cutoff.value)
    (hs : Nat.succ (ProvenanceAddress.depth parent.address) ≤ S.grammar.cutoff.value)
    (hRank : SlotBefore r s) :
    OpenSlotBefore
      { parent := parent, rank := r, childDepthWithinCutoff := hr }
      { parent := parent, rank := s, childDepthWithinCutoff := hs } := by
  change BirthBefore
    (ProvenanceAddress.snoc parent.address r)
    (ProvenanceAddress.snoc parent.address s)
  exact sameParentIncreasingRank parent.address r s hRank

/-- The induced open-slot order is irreflexive. -/
theorem openSlotBefore_irrefl {S : CanonicalBirthSchedule} (slot : OpenBirthSlot S) :
    ¬ OpenSlotBefore slot slot :=
  birthBefore_irrefl (OpenBirthSlot.childAddress slot).address

/-- The induced open-slot order is transitive. -/
theorem openSlotBefore_trans {S : CanonicalBirthSchedule}
    {left middle right : OpenBirthSlot S}
    (h1 : OpenSlotBefore left middle) (h2 : OpenSlotBefore middle right) :
    OpenSlotBefore left right :=
  birthBefore_trans h1 h2

/-- The induced open-slot order is asymmetric. -/
theorem openSlotBefore_asymm {S : CanonicalBirthSchedule}
    {left right : OpenBirthSlot S}
    (h1 : OpenSlotBefore left right) (h2 : OpenSlotBefore right left) : False :=
  birthBefore_asymm h1 h2

/-- Open slots selecting distinct child addresses are comparable. -/
theorem openSlotBefore_total_of_distinct_children {S : CanonicalBirthSchedule}
    {left right : OpenBirthSlot S}
    (hne : (OpenBirthSlot.childAddress left).address ≠
      (OpenBirthSlot.childAddress right).address) :
    OpenSlotBefore left right ∨ OpenSlotBefore right left :=
  birthBefore_total_of_ne hne

end CanonicalBirthSchedule

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
