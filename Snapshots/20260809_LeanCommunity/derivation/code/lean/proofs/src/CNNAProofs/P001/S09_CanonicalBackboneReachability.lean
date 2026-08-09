import CNNAProofs.P001.S08_CanonicalDirectedMatrixStructure

/-!
# P001 R6B.2 — canonical backbone reachability and unconditional birth-cut closure

This module constructs the two path fields of `DirectedCutHypotheses` from the
already-declared C005 bidirectional provenance-parent backbone and the exact M001
port partition.  Interior vertices descend strictly in provenance depth until
the first boundary hit.  The distinguished parent port reaches another boundary
port in one positive edge: its own parent when it is non-root, or the already-born
first root child when the distinguished parent is the root.

The proof introduces no connectivity postulate.  All positive arcs are obtained
from stored C005 `HasConductance` witnesses and transferred through the exact C007
entry theorem of `S08_CanonicalDirectedMatrixStructure`.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CanonicalBirthLocalMeasurementCut
open BirthCutInteriorDomainTheorem
open NextOpenProvenanceSlot
open InterBirthDirectedResponse

/-- `unsnoc?` returns `none` only for the empty provenance word. -/
private theorem eq_nil_of_unsnoc?_eq_none {b : BranchingParameter} :
    ∀ address : ProvenanceAddress b,
      ProvenanceAddress.unsnoc? address = none → address = []
  | [], _ => rfl
  | head :: tail, h => by
      cases hTail : ProvenanceAddress.unsnoc? tail with
      | none =>
          change
            (match ProvenanceAddress.unsnoc? tail with
              | none => some ([], head)
              | some (stem, rank) => some (head :: stem, rank)) = none at h
          rw [hTail] at h
          cases h
      | some pair =>
          cases pair with
          | mk stem rank =>
              change
                (match ProvenanceAddress.unsnoc? tail with
                  | none => some ([], head)
                  | some (rest, finalSlot) => some (head :: rest, finalSlot)) = none at h
              rw [hTail] at h
              cases h

/-- Converse of `ProvenanceAddress.unsnoc?_snoc`, proved by direct recursion on
the word.  This is local definitional infrastructure, not a second parent law. -/
private theorem eq_snoc_of_unsnoc?_eq_some {b : BranchingParameter} :
    ∀ (address parent : ProvenanceAddress b) (localRank : ProvenanceSlot b),
      ProvenanceAddress.unsnoc? address = some (parent, localRank) →
        address = ProvenanceAddress.snoc parent localRank
  | [], parent, localRank, h => by
      change none = some (parent, localRank) at h
      cases h
  | head :: tail, parent, localRank, h => by
      cases hTail : ProvenanceAddress.unsnoc? tail with
      | none =>
          have hTailNil : tail = [] :=
            eq_nil_of_unsnoc?_eq_none tail hTail
          subst tail
          change some ([], head) = some (parent, localRank) at h
          have hPair : ([], head) = (parent, localRank) := Option.some.inj h
          have hParentEq : [] = parent := congrArg Prod.fst hPair
          have hRankEq : head = localRank := congrArg Prod.snd hPair
          calc
            [head] = ProvenanceAddress.snoc [] head := rfl
            _ = ProvenanceAddress.snoc parent localRank := by
              rw [hParentEq, hRankEq]
      | some pair =>
          cases pair with
          | mk stem rank =>
              change
                (match ProvenanceAddress.unsnoc? tail with
                  | none => some ([], head)
                  | some (rest, finalSlot) => some (head :: rest, finalSlot)) =
                  some (parent, localRank) at h
              rw [hTail] at h
              have hPair : (head :: stem, rank) = (parent, localRank) :=
                Option.some.inj h
              have hParentEq : head :: stem = parent := congrArg Prod.fst hPair
              have hRankEq : rank = localRank := congrArg Prod.snd hPair
              have hTailReconstruct :
                  tail = ProvenanceAddress.snoc stem rank :=
                eq_snoc_of_unsnoc?_eq_some tail stem rank hTail
              calc
                head :: tail = head :: ProvenanceAddress.snoc stem rank := by
                  rw [hTailReconstruct]
                _ = ProvenanceAddress.snoc (head :: stem) rank := rfl
                _ = ProvenanceAddress.snoc parent localRank := by
                  rw [hParentEq, hRankEq]

/-- A successful C003 parent lookup reconstructs the child as one exact `snoc`. -/
theorem eq_snoc_of_parent?_eq_some {b : BranchingParameter}
    {child parent : ProvenanceAddress b}
    (hParent : ProvenanceAddress.parent? child = some parent) :
    ∃ localRank : ProvenanceSlot b,
      child = ProvenanceAddress.snoc parent localRank := by
  unfold ProvenanceAddress.parent? at hParent
  cases hUnsnoc : ProvenanceAddress.unsnoc? child with
  | none =>
      rw [hUnsnoc] at hParent
      cases hParent
  | some pair =>
      cases pair with
      | mk recoveredParent localRank =>
          rw [hUnsnoc] at hParent
          have hRecovered : recoveredParent = parent := Option.some.inj hParent
          refine ⟨localRank, ?_⟩
          calc
            child = ProvenanceAddress.snoc recoveredParent localRank :=
              eq_snoc_of_unsnoc?_eq_some child recoveredParent localRank hUnsnoc
            _ = ProvenanceAddress.snoc parent localRank := by
              rw [hRecovered]

/-- Every successful C003 parent lookup strictly decreases provenance depth. -/
theorem depth_parent_lt_of_parent?_eq_some {b : BranchingParameter}
    {child parent : ProvenanceAddress b}
    (hParent : ProvenanceAddress.parent? child = some parent) :
    ProvenanceAddress.depth parent < ProvenanceAddress.depth child := by
  obtain ⟨localRank, hChild⟩ := eq_snoc_of_parent?_eq_some hParent
  rw [hChild, ProvenanceAddress.depth_snoc]
  exact Nat.lt_succ_self _

/-- The penultimate stem occurs in the explicit M001 stem chain. -/
private theorem prefixChainAux_append_singleton_parent_mem {b : BranchingParameter} :
    ∀ (stem rest : ProvenanceAddress b) (localRank : ProvenanceSlot b),
      stem ++ rest ∈
        prefixChainAux stem (rest ++ [localRank])
  | stem, [], localRank => by
      rw [List.append_nil]
      change stem ∈ stem :: prefixChainAux (stem ++ [localRank]) []
      exact List.Mem.head _
  | stem, head :: tail, localRank => by
      change
        stem ++ (head :: tail) ∈
          stem :: prefixChainAux (stem ++ [head]) (tail ++ [localRank])
      apply List.Mem.tail stem
      have hParent := prefixChainAux_append_singleton_parent_mem
        (stem ++ [head]) tail localRank
      have hAppend :
          (stem ++ [head]) ++ tail = stem ++ (head :: tail) :=
        List.append_assoc stem [head] tail
      rw [hAppend] at hParent
      exact hParent

/-- The immediate parent of the distinguished non-root parent address is one of
the M001 causal predecessor ports. -/
theorem immediateParent_mem_causalPredecessorPorts {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {parent : ProvenanceAddress X.grammar.branching}
    (hParent : ProvenanceAddress.parent? (parentAddress next) = some parent) :
    parent ∈ causalPredecessorPorts next := by
  obtain ⟨localRank, hAddress⟩ := eq_snoc_of_parent?_eq_some hParent
  unfold causalPredecessorPorts
  rw [hAddress, snoc_eq_append_singleton]
  exact prefixChainAux_append_singleton_parent_mem [] parent localRank

/-- A stored C005 conductance always has distinct requested endpoint addresses. -/
theorem hasConductance_endpoints_distinct {b : BranchingParameter}
    {edges : List (DirectedConductance b)}
    {source target : ProvenanceAddress b}
    (hConductance : HasConductance edges source target) : source ≠ target := by
  obtain ⟨edge, _hEdge, hSource, hTarget⟩ := hConductance
  intro hEqual
  apply edge.distinct
  exact hSource.trans (hEqual.trans hTarget.symm)

/-- C004A object canonically associated with one C005 state. -/
def firstProvenanceSlotOfState (X : ResponseCapableState) : FirstProvenanceSlot :=
  FirstProvenanceSlot.fromPredecessors X.grammar X.schedule X.schedule_grammar

/-- C005 initial-segment closure forces the structural first root child to be
already born in every response-capable state. -/
theorem firstProvenanceAddress_born {X : ResponseCapableState} :
    FirstProvenanceSlot.address (firstProvenanceSlotOfState X) ∈ X.bornNonRoot := by
  cases hBornList : X.bornNonRoot with
  | nil =>
      exact False.elim (X.bornNonempty hBornList)
  | cons selected tail =>
      have hSelectedBorn : selected ∈ X.bornNonRoot := by
        rw [hBornList]
        exact List.Mem.head tail
      have hSelectedNonroot : ProvenanceAddress.depth selected ≠ 0 :=
        X.bornNonRootOnly selected hSelectedBorn
      have hSelectedCutoff :
          ProvenanceAddress.depth selected ≤ X.grammar.cutoff.value :=
        X.bornWithinCutoff selected hSelectedBorn
      have hOneLeDepth : 1 ≤ ProvenanceAddress.depth selected :=
        Nat.one_le_iff_ne_zero.mpr hSelectedNonroot
      have hFirstCutoff :
          ProvenanceAddress.depth
              (FirstProvenanceSlot.address (firstProvenanceSlotOfState X)) ≤
            X.grammar.cutoff.value := by
        rw [FirstProvenanceSlot.address_depth]
        exact Nat.le_trans hOneLeDepth hSelectedCutoff
      have hFirstNonroot :
          ProvenanceAddress.depth
              (FirstProvenanceSlot.address (firstProvenanceSlotOfState X)) ≠ 0 := by
        rw [FirstProvenanceSlot.address_depth]
        exact Nat.one_ne_zero
      cases FirstProvenanceSlot.address_eq_or_before_nonroot
          (firstProvenanceSlotOfState X) selected hSelectedNonroot with
      | inl hEqual =>
          rw [← hEqual]
          exact List.Mem.head tail
      | inr hBefore =>
          have hFirstBorn := X.bornInitial
            (FirstProvenanceSlot.address (firstProvenanceSlotOfState X))
            selected hSelectedBorn hFirstNonroot hFirstCutoff hBefore
          rw [hBornList] at hFirstBorn
          exact hFirstBorn

/-- If the next child belongs to the root, the already-born structural first
root child is one of M001's older-sibling ports. -/
theorem firstProvenanceAddress_mem_olderSiblingPorts_of_parent_root
    {X : ResponseCapableState} (next : NextOpenSlot X)
    (hParentRoot : parentAddress next = ResponseCapableState.rootAddress X) :
    FirstProvenanceSlot.address (firstProvenanceSlotOfState X) ∈
      olderSiblingPorts next := by
  have hFirstBorn := firstProvenanceAddress_born (X := X)
  have hRankDistinct :
      rank next ≠ FirstProvenanceSlot.firstRank (firstProvenanceSlotOfState X) := by
    intro hRank
    apply child_notBorn next
    have hChild :
        next.val = FirstProvenanceSlot.address (firstProvenanceSlotOfState X) := by
      calc
        next.val = ProvenanceAddress.snoc (parentAddress next) (rank next) :=
          child_eq_snoc next
        _ = ProvenanceAddress.snoc
              (ResponseCapableState.rootAddress X)
              (FirstProvenanceSlot.firstRank (firstProvenanceSlotOfState X)) := by
          rw [hParentRoot, hRank]
        _ = FirstProvenanceSlot.address (firstProvenanceSlotOfState X) := by
          exact (FirstProvenanceSlot.address_eq_snoc
            (firstProvenanceSlotOfState X)).symm
    rw [hChild]
    exact hFirstBorn
  have hRankBefore :
      CanonicalBirthSchedule.SlotBefore
        (FirstProvenanceSlot.firstRank (firstProvenanceSlotOfState X))
        (rank next) := by
    cases FirstProvenanceSlot.firstRank_eq_or_before
        (firstProvenanceSlotOfState X) (rank next) with
    | inl hEqual =>
        exact False.elim (hRankDistinct hEqual)
    | inr hBefore =>
        exact hBefore
  have hRankPositive : 0 < (rank next).val := by
    unfold CanonicalBirthSchedule.SlotBefore at hRankBefore
    rw [FirstProvenanceSlot.firstRank_val] at hRankBefore
    exact hRankBefore
  let earlier : Fin (rank next).val := ⟨0, hRankPositive⟩
  apply List.mem_map.mpr
  refine ⟨earlier, List.mem_finRange earlier, ?_⟩
  have hLocalRank :
      (⟨earlier.val, Nat.lt_trans earlier.isLt (rank next).isLt⟩ :
        ProvenanceSlot X.grammar.branching) =
        FirstProvenanceSlot.firstRank (firstProvenanceSlotOfState X) := by
    apply Fin.eq_of_val_eq
    rfl
  rw [hParentRoot, hLocalRank]
  exact (FirstProvenanceSlot.address_eq_snoc
    (firstProvenanceSlotOfState X)).symm


/-- Convert the raw `List.get` equality returned by `List.get_of_mem` into the
named C007 boundary-coordinate equality without rewriting through a reducible
definition under dependent `Fin` indices. -/
private theorem boundaryAddress_eq_of_get_eq {X : ResponseCapableState}
    {next : NextOpenSlot X}
    {index : Fin (boundary next).length}
    {address : ProvenanceAddress X.grammar.branching}
    (h : (boundary next).get index = address) :
    boundaryAddress next index = address :=
  h

/-- Interior analogue of `boundaryAddress_eq_of_get_eq`. -/
private theorem interiorAddress_eq_of_get_eq {X : ResponseCapableState}
    {next : NextOpenSlot X}
    {index : Fin (CanonicalBirthLocalMeasurementCut.interior next).length}
    {address : ProvenanceAddress X.grammar.branching}
    (h : (CanonicalBirthLocalMeasurementCut.interior next).get index = address) :
    interiorAddress next index = address :=
  h

/-- Interior-to-first-boundary-hit descent along the C005 child-to-parent
conductance.  Recursive calls strictly decrease provenance depth. -/
theorem canonicalInteriorPathToBoundary_aux {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (address : ProvenanceAddress X.grammar.branching)
    (index : Fin (CanonicalBirthLocalMeasurementCut.interior next).length)
    (hAddress : interiorAddress next index = address)
    (hBorn : address ∈ X.bornNonRoot) :
    ∃ boundaryIndex,
      InteriorPathToBoundary realization.blocks index boundaryIndex := by
  obtain ⟨parent, hParent, _hParentToChild, hChildToParent⟩ :=
    X.parentBackbone address hBorn
  have hParentBorn : NodeBorn X.grammar X.bornNonRoot parent := by
    obtain ⟨edge, hEdge, _hSource, hTarget⟩ := hChildToParent
    have hTargetBorn := (X.conductanceEndpointsBorn edge hEdge).2
    rw [hTarget] at hTargetBorn
    exact hTargetBorn
  have hParentCarrier : parent ∈ canonicalCarrier X :=
    born_implies_carrier_mem hParentBorn
  cases carrier_covered next parent hParentCarrier with
  | inl hParentBoundary =>
      obtain ⟨boundaryIndex, hBoundaryGet⟩ := List.get_of_mem hParentBoundary
      have hBoundaryAddress : boundaryAddress next boundaryIndex = parent :=
        boundaryAddress_eq_of_get_eq hBoundaryGet
      have hConductance :
          HasConductance X.conductances
            (canonicalCutAddress next (Sum.inr index))
            (canonicalCutAddress next (Sum.inl boundaryIndex)) := by
        change HasConductance X.conductances
          (interiorAddress next index) (boundaryAddress next boundaryIndex)
        rw [hAddress, hBoundaryAddress]
        exact hChildToParent
      exact ⟨boundaryIndex,
        InteriorPathToBoundary.direct
          (canonicalPositiveArc_of_hasConductance
            realization (Sum.inr index) (Sum.inl boundaryIndex) hConductance)⟩
  | inr hParentInterior =>
      obtain ⟨parentIndex, hParentGet⟩ := List.get_of_mem hParentInterior
      have hParentAddress : interiorAddress next parentIndex = parent :=
        interiorAddress_eq_of_get_eq hParentGet
      have hParentNotRoot :
          parent ≠ ResponseCapableState.rootAddress X := by
        intro hRoot
        have hRootBoundary : ResponseCapableState.rootAddress X ∈ boundary next :=
          birthLocalPort_mem_boundary next (root_is_birthLocalPort next)
        exact boundary_interior_disjoint next
          (ResponseCapableState.rootAddress X) hRootBoundary (hRoot ▸ hParentInterior)
      have hParentBornNonroot : parent ∈ X.bornNonRoot := by
        cases hParentBorn with
        | inl hRoot =>
            exact False.elim (hParentNotRoot hRoot)
        | inr hNonroot =>
            exact hNonroot
      have hConductance :
          HasConductance X.conductances
            (canonicalCutAddress next (Sum.inr index))
            (canonicalCutAddress next (Sum.inr parentIndex)) := by
        change HasConductance X.conductances
          (interiorAddress next index) (interiorAddress next parentIndex)
        rw [hAddress, hParentAddress]
        exact hChildToParent
      obtain ⟨boundaryIndex, hTail⟩ :=
        canonicalInteriorPathToBoundary_aux realization parent parentIndex
          hParentAddress hParentBornNonroot
      exact ⟨boundaryIndex,
        InteriorPathToBoundary.step
          (canonicalPositiveArc_of_hasConductance
            realization (Sum.inr index) (Sum.inr parentIndex) hConductance)
          hTail⟩
termination_by ProvenanceAddress.depth address

decreasing_by
  exact depth_parent_lt_of_parent?_eq_some hParent

/-- Every canonical M001 interior coordinate reaches its first M001 boundary hit
through positive C005 child-to-parent conductances. -/
theorem canonicalEveryInteriorReachesBoundary {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    ∀ index,
      ∃ boundaryIndex,
        InteriorPathToBoundary realization.blocks index boundaryIndex := by
  intro index
  have hInterior : interiorAddress next index ∈
      CanonicalBirthLocalMeasurementCut.interior next :=
    List.get_mem (CanonicalBirthLocalMeasurementCut.interior next) index
  have hBornState := interior_node_born next hInterior
  have hRootBoundary : ResponseCapableState.rootAddress X ∈ boundary next :=
    birthLocalPort_mem_boundary next (root_is_birthLocalPort next)
  have hNotRoot :
      interiorAddress next index ≠ ResponseCapableState.rootAddress X := by
    intro hRoot
    exact boundary_interior_disjoint next
      (ResponseCapableState.rootAddress X) hRootBoundary (hRoot ▸ hInterior)
  have hBorn : interiorAddress next index ∈ X.bornNonRoot := by
    cases hBornState with
    | inl hRoot =>
        exact False.elim (hNotRoot hRoot)
    | inr hNonroot =>
        exact hNonroot
  exact canonicalInteriorPathToBoundary_aux realization
    (interiorAddress next index) index rfl hBorn

/-- The distinguished parent boundary port reaches another canonical M001
boundary port through one positive C005 backbone edge. -/
theorem canonicalDistinguishedReachesOtherBoundary {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next) :
    ∃ other : Fin (boundary next).length,
      other ≠ distinguished.index ∧
        PositivePath realization.blocks
          (Sum.inl distinguished.index) (Sum.inl other) := by
  by_cases hParentRoot :
      parentAddress next = ResponseCapableState.rootAddress X
  · have hOlder :=
      firstProvenanceAddress_mem_olderSiblingPorts_of_parent_root next hParentRoot
    have hFirstBoundary :
        FirstProvenanceSlot.address (firstProvenanceSlotOfState X) ∈ boundary next :=
      birthLocalPort_mem_boundary next (Or.inr hOlder)
    obtain ⟨other, hOtherGet⟩ := List.get_of_mem hFirstBoundary
    have hOtherAddress :
        boundaryAddress next other =
          FirstProvenanceSlot.address (firstProvenanceSlotOfState X) :=
      boundaryAddress_eq_of_get_eq hOtherGet
    have hFirstBorn := firstProvenanceAddress_born (X := X)
    obtain ⟨storedParent, hStoredParent, hForward, _hBackward⟩ :=
      X.parentBackbone
        (FirstProvenanceSlot.address (firstProvenanceSlotOfState X)) hFirstBorn
    have hStoredParentRoot : storedParent = ResponseCapableState.rootAddress X := by
      have hKnownParent :=
        FirstProvenanceSlot.address_parent (firstProvenanceSlotOfState X)
      have hSome :
          some storedParent =
            some (FirstProvenanceSlot.parentAddress (firstProvenanceSlotOfState X)) :=
        hStoredParent.symm.trans hKnownParent
      cases hSome
      exact FirstProvenanceSlot.parentAddress_root (firstProvenanceSlotOfState X)
    have hRootToFirst : HasConductance X.conductances
        (ResponseCapableState.rootAddress X)
        (FirstProvenanceSlot.address (firstProvenanceSlotOfState X)) := by
      rw [← hStoredParentRoot]
      exact hForward
    have hConductance :
        HasConductance X.conductances
          (canonicalCutAddress next (Sum.inl distinguished.index))
          (canonicalCutAddress next (Sum.inl other)) := by
      change HasConductance X.conductances
        (boundaryAddress next distinguished.index) (boundaryAddress next other)
      rw [distinguished.address_eq_parent, hParentRoot, hOtherAddress]
      exact hRootToFirst
    have hOtherDistinct : other ≠ distinguished.index := by
      intro hEqual
      apply hasConductance_endpoints_distinct hConductance
      rw [hEqual]
    exact ⟨other, hOtherDistinct,
      PositivePath.edge
        (canonicalPositiveArc_of_hasConductance realization
          (Sum.inl distinguished.index) (Sum.inl other) hConductance)⟩
  · have hParentBornState := parent_born next
    have hParentBorn : parentAddress next ∈ X.bornNonRoot := by
      cases hParentBornState with
      | inl hRoot =>
          exact False.elim (hParentRoot hRoot)
      | inr hNonroot =>
          exact hNonroot
    obtain ⟨grandparent, hGrandparent, _hUp, hDown⟩ :=
      X.parentBackbone (parentAddress next) hParentBorn
    have hGrandparentCausal : grandparent ∈ causalPredecessorPorts next :=
      immediateParent_mem_causalPredecessorPorts next hGrandparent
    have hGrandparentBoundary : grandparent ∈ boundary next :=
      birthLocalPort_mem_boundary next (Or.inl hGrandparentCausal)
    obtain ⟨other, hOtherGet⟩ := List.get_of_mem hGrandparentBoundary
    have hOtherAddress : boundaryAddress next other = grandparent :=
      boundaryAddress_eq_of_get_eq hOtherGet
    have hConductance :
        HasConductance X.conductances
          (canonicalCutAddress next (Sum.inl distinguished.index))
          (canonicalCutAddress next (Sum.inl other)) := by
      change HasConductance X.conductances
        (boundaryAddress next distinguished.index) (boundaryAddress next other)
      rw [distinguished.address_eq_parent, hOtherAddress]
      exact hDown
    have hOtherDistinct : other ≠ distinguished.index := by
      intro hEqual
      apply hasConductance_endpoints_distinct hConductance
      rw [hEqual]
    exact ⟨other, hOtherDistinct,
      PositivePath.edge
        (canonicalPositiveArc_of_hasConductance realization
          (Sum.inl distinguished.index) (Sum.inl other) hConductance)⟩

/-- All four generic directed-cut hypotheses are derived from the concrete
C005/M001/C007 state data. -/
theorem canonicalDirectedCutHypotheses {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next) :
    DirectedCutHypotheses realization.blocks distinguished.index where
  offDiagonalNonpositive := canonicalBlocks_offDiagonalNonpositive realization
  rowConservative := canonicalBlocks_rowConservative realization
  everyInteriorReachesBoundary := canonicalEveryInteriorReachesBoundary realization
  distinguishedReachesOtherBoundary :=
    canonicalDistinguishedReachesOtherBoundary realization distinguished

/-- R6B closes the actual canonical birth cut without accepting a preassembled
`DirectedCutHypotheses` object as an external premise. -/
theorem canonicalBirthCutClosure_derived {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next) :
    CanonicalBirthCutClosure realization distinguished := by
  exact canonicalBirthCutClosure_of_hypotheses realization distinguished
    (canonicalDirectedCutHypotheses realization distinguished)

/-- Strong canonical-instantiation contract after R6B. -/
def DerivedCanonicalBirthCutClosureContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next),
      CanonicalBirthCutClosure realization distinguished

/-- The stronger R6B contract is inhabited by the state-derived construction. -/
theorem derivedCanonicalBirthCutClosureContract :
    DerivedCanonicalBirthCutClosureContract := by
  intro X next realization distinguished
  exact canonicalBirthCutClosure_derived realization distinguished

/-- P001 contract with a reusable generic theorem and an assumption-free
canonical C005/M001/C007 instantiation. -/
def DerivedPublicContract : Prop :=
  ReusableDirectedClosureContract ∧ DerivedCanonicalBirthCutClosureContract

/-- R6B closes the strengthened P001 public contract. -/
theorem derivedPublicContract : DerivedPublicContract :=
  ⟨reusableDirectedClosureContract, derivedCanonicalBirthCutClosureContract⟩

end CNNAProofs.P001
