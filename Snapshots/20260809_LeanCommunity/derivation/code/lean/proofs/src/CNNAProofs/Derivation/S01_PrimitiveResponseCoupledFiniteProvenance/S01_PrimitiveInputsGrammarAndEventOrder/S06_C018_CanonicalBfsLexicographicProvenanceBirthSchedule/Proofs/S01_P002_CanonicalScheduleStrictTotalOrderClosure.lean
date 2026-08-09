import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule

/-!
P002 — canonical schedule strict-total-order closure.

This proof node packages the static order owned by C018.  It deliberately does
not mention born-state prefixes, unsaturation, least-open existence, or the
executable selector; those state-dependent statements belong to C004 after
C005 has introduced the response-capable state.
-/

namespace CNNAProofs.P002

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- Public P002 closure: the C018 breadth-first/lexicographic relation is a
strict total order on provenance addresses and induces a strict total order on
open-slot selected children, modulo equality of the selected child address. -/
structure CanonicalScheduleStrictTotalOrderClosure : Prop where
  addressIrreflexive :
    ∀ {b : BranchingParameter} (address : ProvenanceAddress b),
      ¬ CanonicalBirthSchedule.BirthBefore address address
  addressTransitive :
    ∀ {b : BranchingParameter} {left middle right : ProvenanceAddress b},
      CanonicalBirthSchedule.BirthBefore left middle →
      CanonicalBirthSchedule.BirthBefore middle right →
      CanonicalBirthSchedule.BirthBefore left right
  addressAsymmetric :
    ∀ {b : BranchingParameter} {left right : ProvenanceAddress b},
      CanonicalBirthSchedule.BirthBefore left right →
      CanonicalBirthSchedule.BirthBefore right left →
      False
  addressTrichotomy :
    ∀ {b : BranchingParameter} (left right : ProvenanceAddress b),
      CanonicalBirthSchedule.BirthBefore left right ∨
      left = right ∨
      CanonicalBirthSchedule.BirthBefore right left
  distinctAddressesComparable :
    ∀ {b : BranchingParameter} {left right : ProvenanceAddress b},
      left ≠ right →
      CanonicalBirthSchedule.BirthBefore left right ∨
      CanonicalBirthSchedule.BirthBefore right left
  slotIrreflexive :
    ∀ {schedule : CanonicalBirthSchedule}
      (slot : CanonicalBirthSchedule.OpenBirthSlot schedule),
      ¬ CanonicalBirthSchedule.OpenSlotBefore slot slot
  slotTransitive :
    ∀ {schedule : CanonicalBirthSchedule}
      {left middle right : CanonicalBirthSchedule.OpenBirthSlot schedule},
      CanonicalBirthSchedule.OpenSlotBefore left middle →
      CanonicalBirthSchedule.OpenSlotBefore middle right →
      CanonicalBirthSchedule.OpenSlotBefore left right
  slotAsymmetric :
    ∀ {schedule : CanonicalBirthSchedule}
      {left right : CanonicalBirthSchedule.OpenBirthSlot schedule},
      CanonicalBirthSchedule.OpenSlotBefore left right →
      CanonicalBirthSchedule.OpenSlotBefore right left →
      False
  slotExtensionalTrichotomy :
    ∀ {schedule : CanonicalBirthSchedule}
      (left right : CanonicalBirthSchedule.OpenBirthSlot schedule),
      CanonicalBirthSchedule.OpenSlotBefore left right ∨
      (CanonicalBirthSchedule.OpenBirthSlot.childAddress left).address =
        (CanonicalBirthSchedule.OpenBirthSlot.childAddress right).address ∨
      CanonicalBirthSchedule.OpenSlotBefore right left

/-- The complete static order closure follows directly from the C018 theorem
chain; P002 introduces no new model assumption. -/
theorem canonicalScheduleStrictTotalOrderClosure :
    CanonicalScheduleStrictTotalOrderClosure where
  addressIrreflexive := by
    intro b address
    exact CanonicalBirthSchedule.birthBefore_irrefl address
  addressTransitive := by
    intro b left middle right hLeftMiddle hMiddleRight
    exact CanonicalBirthSchedule.birthBefore_trans hLeftMiddle hMiddleRight
  addressAsymmetric := by
    intro b left right hLeftRight hRightLeft
    exact CanonicalBirthSchedule.birthBefore_asymm hLeftRight hRightLeft
  addressTrichotomy := by
    intro b left right
    exact CanonicalBirthSchedule.birthBefore_trichotomy left right
  distinctAddressesComparable := by
    intro b left right hDistinct
    exact CanonicalBirthSchedule.birthBefore_total_of_ne hDistinct
  slotIrreflexive := by
    intro schedule slot
    exact CanonicalBirthSchedule.openSlotBefore_irrefl slot
  slotTransitive := by
    intro schedule left middle right hLeftMiddle hMiddleRight
    exact CanonicalBirthSchedule.openSlotBefore_trans hLeftMiddle hMiddleRight
  slotAsymmetric := by
    intro schedule left right hLeftRight hRightLeft
    exact CanonicalBirthSchedule.openSlotBefore_asymm hLeftRight hRightLeft
  slotExtensionalTrichotomy := by
    intro schedule left right
    exact CanonicalBirthSchedule.birthBefore_trichotomy
      (CanonicalBirthSchedule.OpenBirthSlot.childAddress left).address
      (CanonicalBirthSchedule.OpenBirthSlot.childAddress right).address

/-- Generic minimality among an explicitly supplied class of C018 open-slot
records.  This definition is state-free: the predicate supplies the admissible
class, while P002 supplies only the order. -/
def IsMinimalSelectedChild {schedule : CanonicalBirthSchedule}
    (predicate : CanonicalBirthSchedule.OpenBirthSlot schedule → Prop)
    (slot : CanonicalBirthSchedule.OpenBirthSlot schedule) : Prop :=
  predicate slot ∧
    ∀ other, predicate other →
      ¬ CanonicalBirthSchedule.OpenSlotBefore other slot

/-- Two minimal witnesses for one predicate select the same child address.
Record equality is intentionally not claimed because an open-slot record
contains proof-bearing cutoff data; P002 closes the extensional order on the
selected child. -/
theorem minimalSelectedChild_unique
    {schedule : CanonicalBirthSchedule}
    {predicate : CanonicalBirthSchedule.OpenBirthSlot schedule → Prop}
    {left right : CanonicalBirthSchedule.OpenBirthSlot schedule}
    (hLeft : IsMinimalSelectedChild predicate left)
    (hRight : IsMinimalSelectedChild predicate right) :
    (CanonicalBirthSchedule.OpenBirthSlot.childAddress left).address =
      (CanonicalBirthSchedule.OpenBirthSlot.childAddress right).address := by
  by_cases hEqual :
      (CanonicalBirthSchedule.OpenBirthSlot.childAddress left).address =
        (CanonicalBirthSchedule.OpenBirthSlot.childAddress right).address
  · exact hEqual
  · cases CanonicalBirthSchedule.openSlotBefore_total_of_distinct_children hEqual with
    | inl hLeftBeforeRight =>
        exact False.elim (hRight.2 left hLeft.1 hLeftBeforeRight)
    | inr hRightBeforeLeft =>
        exact False.elim (hLeft.2 right hRight.1 hRightBeforeLeft)

/-- Stable public proposition exported by P002. -/
def CanonicalScheduleStrictTotalOrderContract : Prop :=
  CanonicalScheduleStrictTotalOrderClosure

/-- The stable public P002 contract is inhabited. -/
theorem canonicalScheduleStrictTotalOrderContract :
    CanonicalScheduleStrictTotalOrderContract :=
  canonicalScheduleStrictTotalOrderClosure

end CNNAProofs.P002
