import Init.Data.List.FinRange
import Init.Data.List.Lemmas
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S01_C005_ResponseCapableStateSchemaXnNGe1

/-!
Paper 1.3.2 / C004 — next open provenance slot `sₙ₊₁`, `n ≥ 1`.

C004 consumes exactly the C005 recurrent state `Xₙ` and the C018 order already
carried by that state. Lean deliberately does not mirror Python's positional
implementation `schedule.slots[n]`. Instead it identifies the same mathematical
object extensionally: the unique admissible un-born provenance address that is
least under the C018 breadth-first/lexicographic order.

The asymmetry is intentional and locked semantically:

* Python computes the indexed successor of the exact C005 schedule prefix;
* Lean proves existence and uniqueness of the least open C018 address;
* C003 uniquely recovers its provenance parent and final sibling rank.

No geometry, event index, response value, conductance update, birth operation,
or sentinel beyond the finite cutoff is introduced here.

The finite enumeration helper below is proof infrastructure local to C004. It
enumerates only the already-derived finite C003 carrier. Candidate comparison is
still governed exclusively by the already-fixed C018 `BirthBefore` relation, so
no second schedule is defined. No external proof-library dependency, classical
choice, or noncomputable selector is introduced.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

namespace NextOpenProvenanceSlot

/-- Enumerate all provenance words of exactly one intrinsic depth.  This is
proof infrastructure local to C004: it enumerates the already-derived C003
finite carrier and does not define a second scientific schedule. -/
private def addressesAtDepth (b : BranchingParameter) :
    Nat → List (ProvenanceAddress b)
  | 0 => [[]]
  | Nat.succ d =>
      (List.finRange b.value).flatMap fun rank =>
        (addressesAtDepth b d).map fun tail => rank :: tail

/-- Every provenance word occurs in the exact-depth enumeration matching its
word length. -/
private theorem mem_addressesAtDepth_of_length_eq {b : BranchingParameter} :
    ∀ (a : ProvenanceAddress b) (d : Nat),
      a.length = d → a ∈ addressesAtDepth b d
  | [], 0, _ => List.Mem.head []
  | [], Nat.succ d, hLength => by
      cases hLength
  | _ :: _, 0, hLength => by
      cases hLength
  | rank :: tail, Nat.succ d, hLength => by
      have hTailLength : tail.length = d := Nat.succ.inj hLength
      apply List.mem_flatMap_of_mem (List.mem_finRange rank)
      exact List.mem_map_of_mem
        (mem_addressesAtDepth_of_length_eq tail d hTailLength)

/-- Enumerate the complete C003 provenance carrier through cutoff depth `L`,
including the already-born root. -/
private def addressesUpTo (b : BranchingParameter) :
    Nat → List (ProvenanceAddress b)
  | 0 => [[]]
  | Nat.succ L => addressesUpTo b L ++ addressesAtDepth b (Nat.succ L)

/-- Every C003 address inside a finite cutoff occurs in `addressesUpTo`. -/
private theorem mem_addressesUpTo_of_length_le {b : BranchingParameter} :
    ∀ (L : Nat) (a : ProvenanceAddress b),
      a.length ≤ L → a ∈ addressesUpTo b L
  | 0, [], _ => List.Mem.head []
  | 0, _ :: tail, hLength => by
      exact False.elim (Nat.not_succ_le_zero tail.length hLength)
  | Nat.succ L, a, hLength => by
      cases Nat.eq_or_lt_of_le hLength with
      | inl hExact =>
          apply List.mem_append.2
          exact Or.inr
            (mem_addressesAtDepth_of_length_eq a (Nat.succ L) hExact)
      | inr hEarlier =>
          apply List.mem_append.2
          exact Or.inl
            (mem_addressesUpTo_of_length_le L a (Nat.le_of_lt_succ hEarlier))

/-- An address is presently open exactly when it is a non-root C003 address
inside the finite cutoff and is absent from the C005 born prefix. -/
def AdmissibleOpenAddress (X : ResponseCapableState)
    (a : ProvenanceAddress X.grammar.branching) : Prop :=
  ProvenanceAddress.depth a ≠ 0 ∧
    ProvenanceAddress.depth a ≤ X.grammar.cutoff.value ∧
    a ∉ X.bornNonRoot

/-- The finite C005 state has not saturated its admissible provenance carrier. -/
def Unsaturated (X : ResponseCapableState) : Prop :=
  ∃ a : ProvenanceAddress X.grammar.branching, AdmissibleOpenAddress X a

/-- Saturation means that every admissible non-root provenance address is born. -/
def Saturated (X : ResponseCapableState) : Prop :=
  ∀ a : ProvenanceAddress X.grammar.branching,
    ProvenanceAddress.depth a ≠ 0 →
    ProvenanceAddress.depth a ≤ X.grammar.cutoff.value →
    a ∈ X.bornNonRoot

/-- Extensional C004 specification: `a` is open and no other open admissible
address occurs before it in the C018 order. -/
def IsNextOpenAddress (X : ResponseCapableState)
    (a : ProvenanceAddress X.grammar.branching) : Prop :=
  AdmissibleOpenAddress X a ∧
    ∀ earlier : ProvenanceAddress X.grammar.branching,
      AdmissibleOpenAddress X earlier →
      ¬ CanonicalBirthSchedule.BirthBefore earlier a

/-- The C004 object is the proof-bearing unique child address.  Its parent and
rank are recovered below from C003 and therefore are not duplicated fields. -/
abbrev NextOpenSlot (X : ResponseCapableState) :=
  {a : ProvenanceAddress X.grammar.branching // IsNextOpenAddress X a}

/-- C004 exposes the decidability already present in the primitive data:
depth inequalities are decidable on `Nat`, and membership is decidable for the
finite list of `List (Fin b)`.  The explicit instance prevents typeclass
resolution from having to unfold the scientific predicate automatically. -/
private instance admissibleOpenAddressDecidable (X : ResponseCapableState)
    (a : ProvenanceAddress X.grammar.branching) :
    Decidable (AdmissibleOpenAddress X a) := by
  unfold AdmissibleOpenAddress ProvenanceAddress.depth
  infer_instance

/-- C018 `BirthBefore` is likewise decidable from its already-fixed definition:
`Nat.<` decides the breadth-first depth clause and `List.Lex` decides the
equal-depth lexicographic clause from decidable local rank comparison.  This is
proof/implementation infrastructure only; it does not add an ordering rule. -/
private instance birthBeforeDecidable {b : BranchingParameter}
    (a c : ProvenanceAddress b) :
    Decidable (CanonicalBirthSchedule.BirthBefore a c) := by
  unfold CanonicalBirthSchedule.BirthBefore
    CanonicalBirthSchedule.AddressLexBefore
    CanonicalBirthSchedule.SlotBefore
    ProvenanceAddress.depth
  infer_instance

/-- Prefer an open candidate exactly when it lies strictly earlier in the
already-fixed C018 order.  Closed candidates leave the current witness
unchanged. -/
private def preferEarlierOpen (X : ResponseCapableState)
    (current candidate : ProvenanceAddress X.grammar.branching) :
    ProvenanceAddress X.grammar.branching :=
  if _hOpen : AdmissibleOpenAddress X candidate then
    if _hBefore : CanonicalBirthSchedule.BirthBefore candidate current then
      candidate
    else
      current
  else
    current

/-- `current` is open and no open member of `candidates` precedes it. -/
private def MinimalAmong (X : ResponseCapableState)
    (candidates : List (ProvenanceAddress X.grammar.branching))
    (current : ProvenanceAddress X.grammar.branching) : Prop :=
  AdmissibleOpenAddress X current ∧
    ∀ a, a ∈ candidates → AdmissibleOpenAddress X a →
      ¬ CanonicalBirthSchedule.BirthBefore a current

/-- Adding one candidate preserves the least-open invariant. -/
private theorem minimalAmong_cons (X : ResponseCapableState)
    (candidate : ProvenanceAddress X.grammar.branching)
    {rest : List (ProvenanceAddress X.grammar.branching)}
    {current : ProvenanceAddress X.grammar.branching}
    (hMin : MinimalAmong X rest current) :
    MinimalAmong X (candidate :: rest) (preferEarlierOpen X current candidate) := by
  unfold preferEarlierOpen
  split
  next hOpen =>
    split
    next hBefore =>
      constructor
      · exact hOpen
      · intro a ha haOpen
        cases ha with
        | head =>
            exact CanonicalBirthSchedule.birthBefore_irrefl candidate
        | tail _ hTail =>
            intro hABefore
            apply hMin.2 a hTail haOpen
            exact CanonicalBirthSchedule.birthBefore_trans hABefore hBefore
    next hNotBefore =>
      constructor
      · exact hMin.1
      · intro a ha haOpen
        cases ha with
        | head =>
            exact hNotBefore
        | tail _ hTail =>
            exact hMin.2 a hTail haOpen
  next hNotOpen =>
    constructor
    · exact hMin.1
    · intro a ha haOpen
      cases ha with
      | head =>
          exact False.elim (hNotOpen haOpen)
      | tail _ hTail =>
          exact hMin.2 a hTail haOpen

/-- Fold the finite C003 carrier to the earliest admissible open address.
The recursion is structural on a finite list and therefore requires neither
choice nor noncomputable selection. -/
private def leastOpenFrom (X : ResponseCapableState)
    (current : ProvenanceAddress X.grammar.branching) :
    List (ProvenanceAddress X.grammar.branching) →
      ProvenanceAddress X.grammar.branching
  | [] => current
  | candidate :: rest =>
      preferEarlierOpen X (leastOpenFrom X current rest) candidate

/-- The finite fold returns an open address minimal among every candidate in
the supplied list. -/
private theorem leastOpenFrom_minimal (X : ResponseCapableState)
    (current : ProvenanceAddress X.grammar.branching)
    (candidates : List (ProvenanceAddress X.grammar.branching))
    (hCurrent : AdmissibleOpenAddress X current) :
    MinimalAmong X candidates (leastOpenFrom X current candidates) := by
  induction candidates with
  | nil =>
      constructor
      · exact hCurrent
      · intro a ha _hOpen
        cases ha
  | cons candidate rest ih =>
      exact minimalAmong_cons X candidate ih

/-- Whenever the finite state is unsaturated, explicit finite C003 enumeration
and C018 comparison construct the unique least open address.  No classical or
choice-based selector is used. -/
theorem exists_of_unsaturated (X : ResponseCapableState)
    (hOpen : Unsaturated X) : Nonempty (NextOpenSlot X) := by
  obtain ⟨seed, hSeed⟩ := hOpen
  have hMin := leastOpenFrom_minimal X seed
    (addressesUpTo X.grammar.branching X.grammar.cutoff.value) hSeed
  refine ⟨⟨leastOpenFrom X seed
    (addressesUpTo X.grammar.branching X.grammar.cutoff.value), ?_⟩⟩
  constructor
  · exact hMin.1
  · intro earlier hEarlierOpen
    apply hMin.2 earlier
    · exact mem_addressesUpTo_of_length_le
        X.grammar.cutoff.value earlier hEarlierOpen.2.1
    · exact hEarlierOpen

/-- The selected child is non-root. -/
theorem child_nonroot {X : ResponseCapableState} (next : NextOpenSlot X) :
    ProvenanceAddress.depth next.val ≠ 0 :=
  next.property.1.1

/-- The selected child remains inside the finite C003 cutoff. -/
theorem child_withinCutoff {X : ResponseCapableState} (next : NextOpenSlot X) :
    ProvenanceAddress.depth next.val ≤ X.grammar.cutoff.value :=
  next.property.1.2.1

/-- The selected child is not yet part of `Xₙ`. -/
theorem child_notBorn {X : ResponseCapableState} (next : NextOpenSlot X) :
    next.val ∉ X.bornNonRoot :=
  next.property.1.2.2

/-- No admissible open address can lie strictly before the selected child. -/
theorem no_open_before {X : ResponseCapableState} (next : NextOpenSlot X)
    (earlier : ProvenanceAddress X.grammar.branching)
    (hOpen : AdmissibleOpenAddress X earlier) :
    ¬ CanonicalBirthSchedule.BirthBefore earlier next.val :=
  next.property.2 earlier hOpen

/-- Any two C004 witnesses have the same child address. -/
theorem child_unique {X : ResponseCapableState}
    (left right : NextOpenSlot X) : left.val = right.val := by
  by_cases hEq : left.val = right.val
  · exact hEq
  · cases CanonicalBirthSchedule.birthBefore_total_of_ne hEq with
    | inl hLeftBefore =>
        exact False.elim (no_open_before right left.val left.property.1 hLeftBefore)
    | inr hRightBefore =>
        exact False.elim (no_open_before left right.val right.property.1 hRightBefore)

/-- Therefore C004 identifies a unique proof-bearing object, not merely a
minimality class. -/
theorem unique {X : ResponseCapableState} (left right : NextOpenSlot X) :
    left = right :=
  Subtype.ext (child_unique left right)

/-- Every born non-root address lies strictly before the C004 child.  If the
reverse order held, C005 initial-segment closure would force the open child to
be born. -/
theorem born_before_next {X : ResponseCapableState} (next : NextOpenSlot X)
    {a : ProvenanceAddress X.grammar.branching} (ha : a ∈ X.bornNonRoot) :
    CanonicalBirthSchedule.BirthBefore a next.val := by
  have hNe : a ≠ next.val := by
    intro hEq
    apply child_notBorn next
    rw [← hEq]
    exact ha
  cases CanonicalBirthSchedule.birthBefore_total_of_ne hNe with
  | inl hBefore =>
      exact hBefore
  | inr hReverse =>
      have hBornNext : next.val ∈ X.bornNonRoot :=
        X.bornInitial next.val a ha
          (child_nonroot next) (child_withinCutoff next) hReverse
      exact False.elim ((child_notBorn next) hBornNext)

/-- Conversely, every admissible address strictly before the C004 child is
already born.  This is the Lean form of the Python prefix boundary. -/
theorem earlier_admissible_is_born {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (a : ProvenanceAddress X.grammar.branching)
    (hNonroot : ProvenanceAddress.depth a ≠ 0)
    (hCutoff : ProvenanceAddress.depth a ≤ X.grammar.cutoff.value)
    (hBefore : CanonicalBirthSchedule.BirthBefore a next.val) :
    a ∈ X.bornNonRoot := by
  by_cases hBorn : a ∈ X.bornNonRoot
  · exact hBorn
  · have hOpen : AdmissibleOpenAddress X a :=
      ⟨hNonroot, hCutoff, hBorn⟩
    exact False.elim ((no_open_before next a hOpen) hBefore)

/-- On the admissible finite carrier, the C005 born prefix is exactly the set
of C018 predecessors of the C004 child. This is the language-independent
prefix-boundary statement corresponding to Python's `schedule.slots[n]`. -/
theorem admissible_born_iff_before_next {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (a : ProvenanceAddress X.grammar.branching)
    (hNonroot : ProvenanceAddress.depth a ≠ 0)
    (hCutoff : ProvenanceAddress.depth a ≤ X.grammar.cutoff.value) :
    a ∈ X.bornNonRoot ↔ CanonicalBirthSchedule.BirthBefore a next.val := by
  constructor
  · intro hBorn
    exact born_before_next next hBorn
  · intro hBefore
    exact earlier_admissible_is_born next a hNonroot hCutoff hBefore

/-- C003's recursive `snoc` is extensionally ordinary append by one final rank. -/
theorem snoc_eq_append_singleton {b : BranchingParameter}
    (parent : ProvenanceAddress b) (rank : ProvenanceSlot b) :
    ProvenanceAddress.snoc parent rank = parent ++ [rank] := by
  induction parent with
  | nil =>
      rfl
  | cons head tail ih =>
      change head :: ProvenanceAddress.snoc tail rank = head :: (tail ++ [rank])
      rw [ih]

/-- A C004 child is a nonempty provenance word. -/
theorem child_ne_nil {X : ResponseCapableState} (next : NextOpenSlot X) :
    next.val ≠ [] := by
  intro hNil
  apply child_nonroot next
  rw [hNil]
  rfl

/-- Recover the provenance parent from the child word without adding new data. -/
def parentAddress {X : ResponseCapableState} (next : NextOpenSlot X) :
    ProvenanceAddress X.grammar.branching :=
  next.val.dropLast

/-- Recover the final local sibling rank from the same child word. -/
def rank {X : ResponseCapableState} (next : NextOpenSlot X) :
    ProvenanceSlot X.grammar.branching :=
  next.val.getLast (child_ne_nil next)

/-- The recovered C003 parent and rank reconstruct exactly the selected child. -/
theorem child_eq_snoc {X : ResponseCapableState} (next : NextOpenSlot X) :
    next.val = ProvenanceAddress.snoc (parentAddress next) (rank next) := by
  rw [snoc_eq_append_singleton]
  exact (List.dropLast_concat_getLast (child_ne_nil next)).symm

/-- C003's parent selector recovers exactly the C004 parent. -/
theorem child_parent {X : ResponseCapableState} (next : NextOpenSlot X) :
    ProvenanceAddress.parent? next.val = some (parentAddress next) := by
  rw [child_eq_snoc]
  exact ProvenanceAddress.parent?_snoc (parentAddress next) (rank next)

/-- C003's final-slot selector recovers exactly the C004 sibling rank. -/
theorem child_finalSlot {X : ResponseCapableState} (next : NextOpenSlot X) :
    ProvenanceAddress.finalSlot? next.val = some (rank next) := by
  rw [child_eq_snoc]
  exact ProvenanceAddress.finalSlot?_snoc (parentAddress next) (rank next)

/-- A provenance word has depth zero only when it is the C003 root word. -/
theorem eq_root_of_depth_eq_zero {b : BranchingParameter}
    (a : ProvenanceAddress b) (hDepth : ProvenanceAddress.depth a = 0) :
    a = ProvenanceAddress.root b := by
  cases a with
  | nil =>
      rfl
  | cons head tail =>
      change Nat.succ tail.length = 0 at hDepth
      cases hDepth

/-- The parent of the next open child is already present in `Xₙ`.  Otherwise
that parent would itself be an earlier admissible open address, contradicting
C004 minimality. -/
theorem parent_born {X : ResponseCapableState} (next : NextOpenSlot X) :
    NodeBorn X.grammar X.bornNonRoot (parentAddress next) := by
  by_cases hRoot : parentAddress next = ProvenanceAddress.root X.grammar.branching
  · exact Or.inl hRoot
  · apply Or.inr
    by_cases hBorn : parentAddress next ∈ X.bornNonRoot
    · exact hBorn
    · have hParentNonroot :
          ProvenanceAddress.depth (parentAddress next) ≠ 0 := by
        intro hDepth
        exact hRoot (eq_root_of_depth_eq_zero (parentAddress next) hDepth)
      have hChildCutoff := child_withinCutoff next
      rw [child_eq_snoc, ProvenanceAddress.depth_snoc] at hChildCutoff
      have hParentCutoff :
          ProvenanceAddress.depth (parentAddress next) ≤ X.grammar.cutoff.value :=
        Nat.le_trans
          (Nat.le_succ (ProvenanceAddress.depth (parentAddress next)))
          hChildCutoff
      have hParentOpen : AdmissibleOpenAddress X (parentAddress next) :=
        ⟨hParentNonroot, hParentCutoff, hBorn⟩
      have hParentBefore :
          CanonicalBirthSchedule.BirthBefore (parentAddress next) next.val := by
        rw [child_eq_snoc]
        exact CanonicalBirthSchedule.parent_before_child
          (parentAddress next) (rank next)
      exact False.elim ((no_open_before next (parentAddress next) hParentOpen) hParentBefore)

/-- The child address determines the complete parent/rank provenance slot
uniquely.  This is the Lean side of the Python `OpenBirthSlot` identity lock. -/
theorem parent_rank_unique {X : ResponseCapableState} (next : NextOpenSlot X)
    {parent : ProvenanceAddress X.grammar.branching}
    {localRank : ProvenanceSlot X.grammar.branching}
    (hChild : next.val = ProvenanceAddress.snoc parent localRank) :
    parent = parentAddress next ∧ localRank = rank next := by
  have hSlots :
      ProvenanceAddress.snoc parent localRank =
        ProvenanceAddress.snoc (parentAddress next) (rank next) :=
    hChild.symm.trans (child_eq_snoc next)
  exact ⟨ProvenanceAddress.snoc_parent_unique hSlots,
    ProvenanceAddress.snoc_slot_unique hSlots⟩

/-- Unsaturation and saturation cannot both hold. -/
theorem unsaturated_not_saturated (X : ResponseCapableState)
    (hOpen : Unsaturated X) : ¬ Saturated X := by
  intro hSaturated
  obtain ⟨a, hNonroot, hCutoff, hNotBorn⟩ := hOpen
  exact hNotBorn (hSaturated a hNonroot hCutoff)

/-- A saturated finite approximant has no C004 object; there is deliberately no
sentinel successor outside the C003 cutoff. -/
theorem no_next_of_saturated (X : ResponseCapableState)
    (hSaturated : Saturated X) : NextOpenSlot X → False := by
  intro next
  exact (child_notBorn next)
    (hSaturated next.val (child_nonroot next) (child_withinCutoff next))

end NextOpenProvenanceSlot

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
