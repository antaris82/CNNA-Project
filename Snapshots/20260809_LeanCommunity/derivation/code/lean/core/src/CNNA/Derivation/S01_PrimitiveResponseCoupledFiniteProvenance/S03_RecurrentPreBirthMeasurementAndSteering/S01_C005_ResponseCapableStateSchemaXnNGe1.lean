import Init.Data.Rat.Lemmas
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S07_C014_BootstrapStateX1RV1CRV11

/-!
Paper 1.3.1 / C005 — response-capable state schema `Xₙ`, `n ≥ 1`.

C005 defines the domain of the recurrent growth step after the exceptional
bootstrap.  A state carries an already-derived C003 grammar and C018 schedule,
a nonempty finite list of born non-root provenance addresses forming an initial
segment of the canonical order, and positive directed conductances supported on
the born carrier.  Each born non-root address retains positive conductance in
both directions to its provenance parent, so the current carrier is connected
through its provenance backbone and can serve as input to later response cuts.

C005 does not choose the next slot, compute Schur/DtN response, or update the
state.  It also does not yet define record/live update semantics.  Those are
owned by later SOLL nodes.  C014 supplies the base case `X₁`.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

/-- One positive directed conductance on the born provenance carrier. -/
structure DirectedConductance (b : BranchingParameter) where
  source : ProvenanceAddress b
  target : ProvenanceAddress b
  value : Rat
  positive : 0 < value
  distinct : source ≠ target

/-- Root plus the listed born non-root addresses form the current carrier. -/
def NodeBorn (G : FiniteBAryProvenanceGrammar)
    (bornNonRoot : List (ProvenanceAddress G.branching))
    (a : ProvenanceAddress G.branching) : Prop :=
  a = ProvenanceAddress.root G.branching ∨ a ∈ bornNonRoot

/-- A directed conductance list contains the requested ordered pair. -/
def HasConductance {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) : Prop :=
  ∃ edge, edge ∈ edges ∧ edge.source = source ∧ edge.target = target

/-- Two stored conductance entries must not represent the same ordered pair. -/
def DistinctConductancePair {b : BranchingParameter}
    (left right : DirectedConductance b) : Prop :=
  left.source ≠ right.source ∨ left.target ≠ right.target

/-- C005 recurrent-state domain. -/
structure ResponseCapableState where
  grammar : FiniteBAryProvenanceGrammar
  schedule : CanonicalBirthSchedule
  schedule_grammar : schedule.grammar = grammar
  bornNonRoot : List (ProvenanceAddress grammar.branching)
  bornNonempty : bornNonRoot ≠ []
  bornWithinCutoff : ∀ a, a ∈ bornNonRoot →
    ProvenanceAddress.depth a ≤ grammar.cutoff.value
  bornNonRootOnly : ∀ a, a ∈ bornNonRoot → ProvenanceAddress.depth a ≠ 0
  bornOrdered : List.Pairwise CanonicalBirthSchedule.BirthBefore bornNonRoot
  bornInitial : ∀ a c,
    c ∈ bornNonRoot →
    ProvenanceAddress.depth a ≠ 0 →
    ProvenanceAddress.depth a ≤ grammar.cutoff.value →
    CanonicalBirthSchedule.BirthBefore a c →
    a ∈ bornNonRoot
  conductances : List (DirectedConductance grammar.branching)
  conductanceEndpointsBorn : ∀ edge, edge ∈ conductances →
    NodeBorn grammar bornNonRoot edge.source ∧
      NodeBorn grammar bornNonRoot edge.target
  conductancePairsUnique : List.Pairwise DistinctConductancePair conductances
  parentBackbone : ∀ child,
    child ∈ bornNonRoot →
    ∃ parent,
      ProvenanceAddress.parent? child = some parent ∧
      HasConductance conductances parent child ∧
      HasConductance conductances child parent

namespace ResponseCapableState

/-- `n` is the number of born non-root nodes. -/
def n (X : ResponseCapableState) : Nat :=
  X.bornNonRoot.length

/-- Every C005 state satisfies `n ≥ 1`. -/
theorem one_le_n (X : ResponseCapableState) : 1 ≤ n X := by
  unfold n
  cases h : X.bornNonRoot with
  | nil =>
      exact False.elim (X.bornNonempty h)
  | cons a as =>
      change Nat.succ 0 ≤ Nat.succ as.length
      exact Nat.succ_le_succ (Nat.zero_le as.length)

/-- Root address of the state grammar. -/
def rootAddress (X : ResponseCapableState) : ProvenanceAddress X.grammar.branching :=
  ProvenanceAddress.root X.grammar.branching

/-- The root always belongs to the current carrier by definition. -/
theorem rootBorn (X : ResponseCapableState) :
    NodeBorn X.grammar X.bornNonRoot (rootAddress X) :=
  Or.inl rfl

/-- The C014 root and first newborn are distinct. -/
theorem bootstrap_root_ne_newborn (X : BootstrapState) :
    BootstrapState.rootAddress X ≠ BootstrapState.newbornAddress X := by
  intro h
  have hd := congrArg ProvenanceAddress.depth h
  change ProvenanceAddress.depth (FirstProvenanceSlot.parentAddress X.birth.slot) =
    ProvenanceAddress.depth (FirstProvenanceSlot.address X.birth.slot) at hd
  rw [FirstProvenanceSlot.parentAddress_root,
    ProvenanceAddress.depth_root,
    FirstProvenanceSlot.address_depth] at hd
  cases hd

/-- C014's two unit-weighted orientations, now represented on the rational carrier. -/
def bootstrapForwardConductance (X : BootstrapState) :
    DirectedConductance X.birth.slot.grammar.branching where
  source := BootstrapState.rootAddress X
  target := BootstrapState.newbornAddress X
  value := ((FirstNonRootBirth.directedConductances X.birth).1 : Rat)
  positive := by
    rw [FirstNonRootBirth.directedConductances_eq_unit_pair X.birth]
    exact (Rat.natCast_pos).2 (Nat.zero_lt_succ 0)
  distinct := bootstrap_root_ne_newborn X

/-- Reverse orientation of the C014 unit relation. -/
def bootstrapBackwardConductance (X : BootstrapState) :
    DirectedConductance X.birth.slot.grammar.branching where
  source := BootstrapState.newbornAddress X
  target := BootstrapState.rootAddress X
  value := ((FirstNonRootBirth.directedConductances X.birth).2 : Rat)
  positive := by
    rw [FirstNonRootBirth.directedConductances_eq_unit_pair X.birth]
    exact (Rat.natCast_pos).2 (Nat.zero_lt_succ 0)
  distinct := (bootstrap_root_ne_newborn X).symm

/-- The forward C005 base conductance is the rational lift of C014's stored value. -/
theorem base_case_transports_c014_forward_value (X : BootstrapState) :
    (bootstrapForwardConductance X).value =
      ((FirstNonRootBirth.directedConductances X.birth).1 : Rat) :=
  rfl

/-- The backward C005 base conductance is the rational lift of C014's stored value. -/
theorem base_case_transports_c014_backward_value (X : BootstrapState) :
    (bootstrapBackwardConductance X).value =
      ((FirstNonRootBirth.directedConductances X.birth).2 : Rat) :=
  rfl

/-- The singleton C014 birth history is pairwise ordered. -/
theorem bootstrap_bornOrdered (X : BootstrapState) :
    List.Pairwise CanonicalBirthSchedule.BirthBefore [BootstrapState.newbornAddress X] := by
  apply List.Pairwise.cons
  · intro a ha
    cases ha
  · exact List.Pairwise.nil

/-- C014's first newborn is the initial non-root segment of the C018 order. -/
theorem bootstrap_bornInitial (X : BootstrapState) :
    ∀ a c,
      c ∈ [BootstrapState.newbornAddress X] →
      ProvenanceAddress.depth a ≠ 0 →
      ProvenanceAddress.depth a ≤ X.birth.slot.grammar.cutoff.value →
      CanonicalBirthSchedule.BirthBefore a c →
      a ∈ [BootstrapState.newbornAddress X] := by
  intro a c hc hnonroot _hcut hBefore
  cases hc with
  | head =>
      cases FirstProvenanceSlot.address_eq_or_before_nonroot X.birth.slot a hnonroot with
      | inl hEq =>
          cases hEq
          exact List.Mem.head []
      | inr hAfter =>
          exact False.elim (CanonicalBirthSchedule.birthBefore_asymm hBefore hAfter)
  | tail _ hTail =>
      cases hTail

/-- The two C014 conductances have distinct ordered endpoint pairs. -/
theorem bootstrap_conductancePairsUnique (X : BootstrapState) :
    List.Pairwise DistinctConductancePair
      [bootstrapForwardConductance X, bootstrapBackwardConductance X] := by
  apply List.Pairwise.cons
  · intro edge hEdge
    cases hEdge with
    | head =>
        exact Or.inl (bootstrap_root_ne_newborn X)
    | tail _ hTail =>
        cases hTail
  · apply List.Pairwise.cons
    · intro edge hEdge
      cases hEdge
    · exact List.Pairwise.nil

/-- The exceptional bootstrap state `X₁` inhabits the recurrent C005 schema. -/
def fromBootstrap (X : BootstrapState) : ResponseCapableState where
  grammar := X.birth.slot.grammar
  schedule := X.birth.slot.schedule
  schedule_grammar := X.birth.slot.schedule_grammar
  bornNonRoot := [BootstrapState.newbornAddress X]
  bornNonempty := by
    intro h
    cases h
  bornWithinCutoff := by
    intro a ha
    cases ha with
    | head =>
        exact X.birth.withinCutoff
    | tail _ hTail =>
        cases hTail
  bornNonRootOnly := by
    intro a ha
    cases ha with
    | head =>
        change ProvenanceAddress.depth (FirstProvenanceSlot.address X.birth.slot) ≠ 0
        rw [FirstProvenanceSlot.address_depth]
        exact Nat.one_ne_zero
    | tail _ hTail =>
        cases hTail
  bornOrdered := bootstrap_bornOrdered X
  bornInitial := bootstrap_bornInitial X
  conductances := [bootstrapForwardConductance X, bootstrapBackwardConductance X]
  conductanceEndpointsBorn := by
    intro edge hEdge
    cases hEdge with
    | head =>
        exact ⟨Or.inl rfl, Or.inr (List.Mem.head [])⟩
    | tail _ hTail =>
        cases hTail with
        | head =>
            exact ⟨Or.inr (List.Mem.head []), Or.inl rfl⟩
        | tail _ hNil =>
            cases hNil
  conductancePairsUnique := bootstrap_conductancePairsUnique X
  parentBackbone := by
    intro child hChild
    cases hChild with
    | head =>
        refine ⟨BootstrapState.rootAddress X, ?_, ?_, ?_⟩
        · exact FirstNonRootBirth.newborn_parent_root X.birth
        · refine ⟨bootstrapForwardConductance X, List.Mem.head _, rfl, rfl⟩
        · refine ⟨bootstrapBackwardConductance X, List.Mem.tail _ (List.Mem.head []), rfl, rfl⟩
    | tail _ hTail =>
        cases hTail

/-- The recurrent schema embeds C014 exactly at birth count one. -/
theorem fromBootstrap_n (X : BootstrapState) : n (fromBootstrap X) = 1 :=
  rfl

end ResponseCapableState

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
