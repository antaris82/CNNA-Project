import Init.Data.List.Pairwise
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S01A_C005_ConductanceAppendClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S02A_C004_SuccessorBornPrefixClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S03A_C006_ExactFractionRatRealizationClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S06A_C007_StateDirectedBlockRealizationClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S10A_M004_LiveUpdateSupportClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S04_C009_CodomainStateX

/-!
Paper 1.4.5 / T002 — recurrent state closure theorem.

T002 is the load-bearing one-step closure theorem.  All field-local facts used
below are imported from their semantic owners: C004 closes the successor born
prefix, C005 supplies generic append preservation, C006 realizes exact fractions
as rational conductances, M001/M004 close the provenance support of the live
delta, and C009 supplies the deterministic raw codomain assembly.

T002 itself proves only the cross-interface facts that first arise here:

* exact realization of M004 live updates as positive C005 conductances;
* old/new ordered-pair disjointness;
* assembly of the complete successor C005 state; and
* post-step C005↔C017 coherence, making the next C009 step well typed.

No field-local closure theorem is hidden in this module.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCapableState
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.BirthLocalSchurDtnPrimitive
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.CanonicalBirthLocalMeasurementCut
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.InterBirthDirectedResponse
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.CanonicalResponseSteeringFunctionalSigmaBRnS
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB
open RecordLiveResponseCoupledUpdate
open CodomainStateX

namespace RecurrentStateClosureTheorem

/-- A relation update can be re-entered into C005 precisely when its exact
value is strictly positive and its endpoints are distinct. -/
def RelationUpdateAdmissible {b : BranchingParameter}
    (update : DirectedRelationUpdate b) : Prop :=
  0 < update.value.num ∧ update.source ≠ update.target

/-- C006's canonical rational realization of one admissible relation update. -/
def relationUpdateAsConductance {b : BranchingParameter}
    (update : DirectedRelationUpdate b)
    (h : RelationUpdateAdmissible update) : DirectedConductance b where
  source := update.source
  target := update.target
  value := ExactFraction.toRat update.value
  positive := ExactFraction.toRat_pos_of_num_pos h.1
  distinct := h.2

/-- Proof-preserving ordered realization of an exact relation-update list as
C005 rational conductances. -/
def realizeRelationUpdates {b : BranchingParameter} :
    (updates : List (DirectedRelationUpdate b)) →
    (∀ update, update ∈ updates → RelationUpdateAdmissible update) →
    List (DirectedConductance b)
  | [], _ => []
  | update :: rest, hAdmissible =>
      relationUpdateAsConductance update
          (hAdmissible update (List.Mem.head rest)) ::
        realizeRelationUpdates rest
          (fun candidate hMem =>
            hAdmissible candidate (List.Mem.tail update hMem))

/-- Every realized conductance comes from one relation update with exactly the
same ordered endpoints and the C006 rational value. -/
theorem realizeRelationUpdates_mem_origin {b : BranchingParameter} :
    ∀ (updates : List (DirectedRelationUpdate b))
      (hAdmissible : ∀ update, update ∈ updates → RelationUpdateAdmissible update)
      (edge : DirectedConductance b),
      edge ∈ realizeRelationUpdates updates hAdmissible →
        ∃ update, update ∈ updates ∧
          edge.source = update.source ∧
          edge.target = update.target ∧
          edge.value = ExactFraction.toRat update.value := by
  intro updates
  induction updates with
  | nil =>
      intro hAdmissible edge hEdge
      cases hEdge
  | cons head tail ih =>
      intro hAdmissible edge hEdge
      change edge ∈
        relationUpdateAsConductance head
            (hAdmissible head (List.Mem.head tail)) ::
          realizeRelationUpdates tail
            (fun candidate hMem =>
              hAdmissible candidate (List.Mem.tail head hMem)) at hEdge
      have hCases := List.mem_cons.mp hEdge
      cases hCases with
      | inl hHead =>
          refine ⟨head, List.Mem.head tail, ?_, ?_, ?_⟩
          · rw [hHead]
            rfl
          · rw [hHead]
            rfl
          · rw [hHead]
            rfl
      | inr hTail =>
          obtain ⟨update, hUpdate, hSource, hTarget, hValue⟩ :=
            ih
              (fun candidate hMem =>
                hAdmissible candidate (List.Mem.tail head hMem))
              edge hTail
          exact ⟨update, List.Mem.tail head hUpdate,
            hSource, hTarget, hValue⟩

/-- Every raw relation update yields the corresponding ordered conductance in
its proof-preserving realization. -/
theorem hasConductance_realizeRelationUpdates_of_mem {b : BranchingParameter} :
    ∀ (updates : List (DirectedRelationUpdate b))
      (hAdmissible : ∀ update, update ∈ updates → RelationUpdateAdmissible update)
      (update : DirectedRelationUpdate b),
      update ∈ updates →
        HasConductance (realizeRelationUpdates updates hAdmissible)
          update.source update.target := by
  intro updates
  induction updates with
  | nil =>
      intro hAdmissible update hMem
      cases hMem
  | cons head tail ih =>
      intro hAdmissible update hMem
      have hCases := List.mem_cons.mp hMem
      cases hCases with
      | inl hHead =>
          rw [hHead]
          refine ⟨relationUpdateAsConductance head
              (hAdmissible head (List.Mem.head tail)),
            List.Mem.head _, rfl, rfl⟩
      | inr hTail =>
          obtain ⟨edge, hEdge, hSource, hTarget⟩ :=
            ih
              (fun candidate hCandidate =>
                hAdmissible candidate (List.Mem.tail head hCandidate))
              update hTail
          refine ⟨edge, List.Mem.tail _ hEdge, hSource, hTarget⟩

/-- Exact-value coherence of the rational realization. -/
theorem realizeRelationUpdates_sameValue {b : BranchingParameter} :
    ∀ (updates : List (DirectedRelationUpdate b))
      (hAdmissible : ∀ update, update ∈ updates → RelationUpdateAdmissible update),
      DirectedRelationUpdatesSameValue updates
        ((realizeRelationUpdates updates hAdmissible).map
          directedConductanceAsUpdate) := by
  intro updates
  induction updates with
  | nil =>
      intro hAdmissible
      exact DirectedRelationUpdatesSameValue.nil
  | cons head tail ih =>
      intro hAdmissible
      change DirectedRelationUpdatesSameValue
        (head :: tail)
        (directedConductanceAsUpdate
            (relationUpdateAsConductance head
              (hAdmissible head (List.Mem.head tail))) ::
          (realizeRelationUpdates tail
            (fun candidate hMem =>
              hAdmissible candidate (List.Mem.tail head hMem))).map
                directedConductanceAsUpdate)
      apply DirectedRelationUpdatesSameValue.cons
      · exact {
          source_eq := rfl
          target_eq := rfl
          value_same := ExactFraction.toRat_represents head.value }
      · exact ih
          (fun candidate hMem =>
            hAdmissible candidate (List.Mem.tail head hMem))

/-- Ordered-pair uniqueness survives exact-to-rational realization because the
conversion changes no endpoint. -/
theorem realizeRelationUpdates_pairwise_distinct {b : BranchingParameter} :
    ∀ (updates : List (DirectedRelationUpdate b))
      (hAdmissible : ∀ update, update ∈ updates → RelationUpdateAdmissible update),
      List.Pairwise DistinctRelationPair updates →
        List.Pairwise DistinctConductancePair
          (realizeRelationUpdates updates hAdmissible) := by
  intro updates
  induction updates with
  | nil =>
      intro hAdmissible hPairs
      exact List.Pairwise.nil
  | cons head tail ih =>
      intro hAdmissible hPairs
      apply List.Pairwise.cons
      · intro edge hEdge
        obtain ⟨update, hUpdate, hSource, hTarget, _hValue⟩ :=
          realizeRelationUpdates_mem_origin tail
            (fun candidate hMem =>
              hAdmissible candidate (List.Mem.tail head hMem))
            edge hEdge
        have hRaw := List.rel_of_pairwise_cons hPairs hUpdate
        cases hRaw with
        | inl hSourceNe =>
            apply Or.inl
            rw [hSource]
            exact hSourceNe
        | inr hTargetNe =>
            apply Or.inr
            rw [hTarget]
            exact hTargetNe
      · exact ih
          (fun candidate hMem =>
            hAdmissible candidate (List.Mem.tail head hMem))
          hPairs.of_cons

/-- M004's active live delta satisfies the generic T002 realization predicate. -/
theorem canonicalDelta_admissible {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ update, update ∈ liveRelationDelta next value →
      RelationUpdateAdmissible update := by
  intro update hUpdate
  exact ⟨liveRelationDelta_positiveNum next value hPositive update hUpdate,
    liveRelationDelta_endpoints_distinct next value hUpdate⟩

/-- Rational C005 conductance block corresponding exactly to the M004 live delta. -/
def realizedLiveDelta {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    List (DirectedConductance X.grammar.branching) :=
  realizeRelationUpdates (liveRelationDelta next value)
    (canonicalDelta_admissible next value hPositive)

/-- The realized new block has no duplicate ordered pair. -/
theorem realizedLiveDelta_pairwise_distinct {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    List.Pairwise DistinctConductancePair
      (realizedLiveDelta next value hPositive) := by
  exact realizeRelationUpdates_pairwise_distinct
    (liveRelationDelta next value)
    (canonicalDelta_admissible next value hPositive)
    (liveRelationDelta_pairwise_distinct next value)

/-- Every rationalized new conductance is supported on the successor carrier. -/
theorem realizedLiveDelta_endpointsBorn {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ edge, edge ∈ realizedLiveDelta next value hPositive →
      NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) edge.source ∧
      NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) edge.target := by
  intro edge hEdge
  obtain ⟨update, hUpdate, hSource, hTarget, _hValue⟩ :=
    realizeRelationUpdates_mem_origin
      (liveRelationDelta next value)
      (canonicalDelta_admissible next value hPositive)
      edge hEdge
  have hBorn := liveRelationDelta_endpointsBorn next value hUpdate
  rw [hSource, hTarget]
  exact hBorn

/-- Every new rational conductance touches the newly selected child. -/
theorem realizedLiveDelta_touches_child {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ edge, edge ∈ realizedLiveDelta next value hPositive →
      edge.source = next.val ∨ edge.target = next.val := by
  intro edge hEdge
  obtain ⟨update, hUpdate, hSource, hTarget, _hValue⟩ :=
    realizeRelationUpdates_mem_origin
      (liveRelationDelta next value)
      (canonicalDelta_admissible next value hPositive)
      edge hEdge
  have hTouch := liveRelationDelta_touches_child next value hUpdate
  cases hTouch with
  | inl hSourceChild =>
      exact Or.inl (hSource.trans hSourceChild)
  | inr hTargetChild =>
      exact Or.inr (hTarget.trans hTargetChild)

/-- The two new provenance-backbone orientations survive rational realization. -/
theorem realizedLiveDelta_parentBackbone {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    HasConductance (realizedLiveDelta next value hPositive)
        (parentAddress next) next.val ∧
      HasConductance (realizedLiveDelta next value hPositive)
        next.val (parentAddress next) := by
  have hRaw := parentBackbone_updates_mem_liveRelationDelta next value
  constructor
  · exact hasConductance_realizeRelationUpdates_of_mem
      (liveRelationDelta next value)
      (canonicalDelta_admissible next value hPositive)
      (directRelationUpdate (parentAddress next) next.val value)
      hRaw.1
  · exact hasConductance_realizeRelationUpdates_of_mem
      (liveRelationDelta next value)
      (canonicalDelta_admissible next value hPositive)
      (directRelationUpdate next.val (parentAddress next) value)
      hRaw.2

/-- Old C005 ordered pairs and new M004 ordered pairs cannot collide: every new
pair touches the C004 child while no old endpoint equals that still-unborn child. -/
theorem old_new_conductancePairs_distinct {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ oldEdge, oldEdge ∈ X.conductances →
      ∀ newEdge, newEdge ∈ realizedLiveDelta next value hPositive →
        DistinctConductancePair oldEdge newEdge := by
  intro oldEdge hOld newEdge hNew
  have hOldBorn := X.conductanceEndpointsBorn oldEdge hOld
  have hTouch := realizedLiveDelta_touches_child next value hPositive newEdge hNew
  cases hTouch with
  | inl hSourceChild =>
      apply Or.inl
      intro hEq
      have hChildOld : next.val = oldEdge.source := by
        calc
          next.val = newEdge.source := hSourceChild.symm
          _ = oldEdge.source := hEq.symm
      exact (child_ne_oldNodeBorn next hOldBorn.1) hChildOld
  | inr hTargetChild =>
      apply Or.inr
      intro hEq
      have hChildOld : next.val = oldEdge.target := by
        calc
          next.val = newEdge.target := hTargetChild.symm
          _ = oldEdge.target := hEq.symm
      exact (child_ne_oldNodeBorn next hOldBorn.2) hChildOld

/-- Complete C005 conductance list for the successor. -/
def successorConductances {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    List (DirectedConductance X.grammar.branching) :=
  X.conductances ++ realizedLiveDelta next value hPositive

/-- The complete successor conductance list is pairwise unique. -/
theorem successorConductances_pairwise {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    List.Pairwise DistinctConductancePair
      (successorConductances next value hPositive) := by
  exact conductancePairsUnique_append
    X.conductancePairsUnique
    (realizedLiveDelta_pairwise_distinct next value hPositive)
    (old_new_conductancePairs_distinct next value hPositive)

/-- Every endpoint in the complete successor conductance list is born. -/
theorem successorConductances_endpointsBorn {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ edge, edge ∈ successorConductances next value hPositive →
      NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) edge.source ∧
      NodeBorn X.grammar (X.bornNonRoot ++ [next.val]) edge.target := by
  intro edge hEdge
  have hCases := List.mem_append.mp hEdge
  cases hCases with
  | inl hOld =>
      have hBorn := X.conductanceEndpointsBorn edge hOld
      exact ⟨nodeBorn_append_left hBorn.1, nodeBorn_append_left hBorn.2⟩
  | inr hNew =>
      exact realizedLiveDelta_endpointsBorn next value hPositive edge hNew

/-- Every old provenance-backbone relation persists, and the C004 child gains
both direct parent orientations from M004. -/
theorem successor_parentBackbone {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    ∀ child, child ∈ X.bornNonRoot ++ [next.val] →
      ∃ parent,
        ProvenanceAddress.parent? child = some parent ∧
        HasConductance (successorConductances next value hPositive) parent child ∧
        HasConductance (successorConductances next value hPositive) child parent := by
  intro child hChild
  have hCases := List.mem_append.mp hChild
  cases hCases with
  | inl hOld =>
      obtain ⟨parent, hParent, hForward, hBackward⟩ := X.parentBackbone child hOld
      exact ⟨parent, hParent,
        hasConductance_append_left hForward,
        hasConductance_append_left hBackward⟩
  | inr hNew =>
      have hEq : child = next.val := List.mem_singleton.mp hNew
      rw [hEq]
      have hBackbone := realizedLiveDelta_parentBackbone next value hPositive
      exact ⟨parentAddress next, child_parent next,
        hasConductance_append_right hBackbone.1,
        hasConductance_append_right hBackbone.2⟩

/-- Proof-bearing active T002 input.  The exact M004 instruction is computed,
not supplied as a second growth law. -/
structure RecurrentStepInput (X : ResponseCapableState)
    (next : NextOpenSlot X) where
  channels : RecordLiveChannels X.grammar.branching
  live_coherent : StateChannelCoherent X channels
  response : ExactFractionMatrix (boundary next).length (boundary next).length
  value : ExactFraction
  pair : IsResponseSteeringPair
    (canonicalStateDirectedBlockRealization next) response value
  positive : PositiveSteering value

/-- The unique active M004 instruction associated with the proof-bearing T002
input. -/
def instruction {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : RecurrentStepInput X next) : ResponseCoupledBirthInstruction next :=
  birthLaw (canonicalStateDirectedBlockRealization next)
    input.response input.value input.pair input.positive

/-- C009 input obtained without adding any new field or update law. -/
def codomainInput {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : RecurrentStepInput X next) : CodomainAssemblyInput X next where
  channels := input.channels
  instruction := instruction input
  live_coherent := input.live_coherent

/-- C009 raw codomain consumed by T002. -/
def rawCodomain {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : RecurrentStepInput X next) : CodomainStateData X next :=
  assemble (codomainInput input)

/-- The recurrent successor state.  Every proof field is supplied by its
origin-owned closure plus the T002 cross-interface append arguments above. -/
def successorState {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : RecurrentStepInput X next) : ResponseCapableState where
  grammar := X.grammar
  schedule := X.schedule
  schedule_grammar := X.schedule_grammar
  bornNonRoot := X.bornNonRoot ++ [next.val]
  bornNonempty := (successorBornPrefixClosure next).nonempty
  bornWithinCutoff := (successorBornPrefixClosure next).withinCutoff
  bornNonRootOnly := (successorBornPrefixClosure next).nonRootOnly
  bornOrdered := (successorBornPrefixClosure next).ordered
  bornInitial := (successorBornPrefixClosure next).initial
  conductances := successorConductances next input.value input.positive
  conductanceEndpointsBorn :=
    successorConductances_endpointsBorn next input.value input.positive
  conductancePairsUnique :=
    successorConductances_pairwise next input.value input.positive
  parentBackbone := successor_parentBackbone next input.value input.positive

/-- T002 consumes C009 literally on schedule and born-prefix data. -/
theorem successor_matches_rawCodomain {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : RecurrentStepInput X next) :
    (rawCodomain input).schedule = (successorState input).schedule ∧
    (rawCodomain input).bornNonRoot = (successorState input).bornNonRoot := by
  exact ⟨rfl, rfl⟩

/-- The rationalized new block exactly represents the M004 live delta. -/
theorem realizedLiveDelta_sameValue {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction)
    (hPositive : PositiveSteering value) :
    DirectedRelationUpdatesSameValue
      (liveRelationDelta next value)
      ((realizedLiveDelta next value hPositive).map
        directedConductanceAsUpdate) := by
  exact realizeRelationUpdates_sameValue
    (liveRelationDelta next value)
    (canonicalDelta_admissible next value hPositive)

/-- The updated C017 channel is again coherent with the new C005 conductance
list.  This is the handoff that makes the next C009 step formally available. -/
theorem successor_live_coherent {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : RecurrentStepInput X next) :
    StateChannelCoherent (successorState input)
      (@applyInstruction X next input.channels (instruction input)) := by
  change DirectedRelationUpdatesSameValue
    ((@applyInstruction X next input.channels (instruction input)).live)
    ((X.conductances ++ realizedLiveDelta next input.value input.positive).map
      directedConductanceAsUpdate)
  rw [applyInstruction_live_eq, List.map_append]
  exact directedRelationUpdatesSameValue_append
    input.live_coherent
    (realizedLiveDelta_sameValue next input.value input.positive)

/-- Exact C009 record/live data are the channels handed to the next recurrent
step. -/
theorem rawCodomain_channels_eq {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : RecurrentStepInput X next) :
    (rawCodomain input).record =
        (@applyInstruction X next input.channels (instruction input)).record ∧
      (rawCodomain input).live =
        (@applyInstruction X next input.channels (instruction input)).live := by
  exact ⟨rfl, rfl⟩

/-- Extensional recurrent-successor predicate for one fixed T002 input. -/
def IsRecurrentSuccessor {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : RecurrentStepInput X next) (output : ResponseCapableState) : Prop :=
  output = successorState input

/-- Every proof-bearing active recurrent step has exactly one C005 successor. -/
theorem recurrentSuccessor_existsUnique {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : RecurrentStepInput X next) :
    ∃ output : ResponseCapableState,
      IsRecurrentSuccessor input output ∧
      ∀ other : ResponseCapableState,
        IsRecurrentSuccessor input other → other = output := by
  refine ⟨successorState input, rfl, ?_⟩
  intro other hOther
  exact hOther

/-- Complete Core T002 closure: C009 compatibility, re-entry into C005,
post-live coherence, and deterministic uniqueness. -/
structure RecurrentStateClosure {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : RecurrentStepInput X next) : Prop where
  rawMatchesState :
    (rawCodomain input).schedule = (successorState input).schedule ∧
    (rawCodomain input).bornNonRoot = (successorState input).bornNonRoot
  rawMatchesChannels :
    (rawCodomain input).record =
        (@applyInstruction X next input.channels (instruction input)).record ∧
    (rawCodomain input).live =
        (@applyInstruction X next input.channels (instruction input)).live
  nextLiveCoherent :
    StateChannelCoherent (successorState input)
      (@applyInstruction X next input.channels (instruction input))
  successorUnique :
    ∃ output : ResponseCapableState,
      IsRecurrentSuccessor input output ∧
      ∀ other : ResponseCapableState,
        IsRecurrentSuccessor input other → other = output

/-- T002 is closed for every active positive response-steering input. -/
theorem recurrentStateClosure {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : RecurrentStepInput X next) :
    RecurrentStateClosure input where
  rawMatchesState := successor_matches_rawCodomain input
  rawMatchesChannels := rawCodomain_channels_eq input
  nextLiveCoherent := successor_live_coherent input
  successorUnique := recurrentSuccessor_existsUnique input

/-- Public Core T002 contract. -/
def RecurrentStateClosureContract : Prop :=
  ∀ {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : RecurrentStepInput X next), RecurrentStateClosure input

/-- The derived recurrent step inhabits the complete Core T002 contract. -/
theorem recurrentStateClosureContract : RecurrentStateClosureContract := by
  intro X next input
  exact recurrentStateClosure input

end RecurrentStateClosureTheorem

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
