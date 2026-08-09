import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S10_M004_ResponseCoupledBirthLawBirthlawB

/-!
Paper 1.4.1 / C008 — record/live response-coupled update.

C008 is the deterministic application boundary for the immutable M004 birth
instruction.  It introduces the first explicit separation between historical
birth-record relations and the current live response network.

* `record` preserves all earlier entries and appends only the two direct
  parent/newborn relations created at this birth;
* `live` preserves all earlier entries and appends the same direct relations
  plus M004's strict-ancestor and earlier-sibling backreaction relations.

No response is recomputed here and no rank, rank distance, depth attenuation,
mode, fitted coefficient, node-load scalar, or independent bias is introduced.
C008 also does not yet construct the next C005 `ResponseCapableState`; that
finite schema closure belongs to C009/T002.

The historical Legacy implementation motivated the record/live distinction,
but its free coefficients and node-load mutation are intentionally absent.
The definitions below are reconstructed solely from the current M004 handoff.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.BirthLocalSchurDtnPrimitive
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB

namespace RecordLiveResponseCoupledUpdate

/-- The two physics-carrying relation channels at one finite growth stage.
Lists are append-only histories at C008; downstream nodes may derive current
matrix representations from them. -/
structure RecordLiveChannels (b : BranchingParameter) where
  record : List (DirectedRelationUpdate b)
  live : List (DirectedRelationUpdate b)

/-- Exact representation of a positive C005 conductance as one C008 relation
entry.  This map is used only to initialize the exceptional C014 base state. -/
def directedConductanceAsUpdate {b : BranchingParameter}
    (edge : DirectedConductance b) : DirectedRelationUpdate b where
  source := edge.source
  target := edge.target
  value := ExactFraction.ofRat edge.value

/-- The C014/C005 base relation pair, represented in C008 exact-fraction form. -/
def bootstrapRelationUpdates (X : BootstrapState) :
    List (DirectedRelationUpdate X.birth.slot.grammar.branching) :=
  [ directedConductanceAsUpdate (ResponseCapableState.bootstrapForwardConductance X),
    directedConductanceAsUpdate (ResponseCapableState.bootstrapBackwardConductance X) ]

/-- At `X₁`, record and live start from the same already-derived C014 relation
pair.  This is bootstrap-specific: C008 never snapshots a later live network
back into record history. -/
def bootstrapRecordLiveChannels (X : BootstrapState) :
    RecordLiveChannels X.birth.slot.grammar.branching where
  record := bootstrapRelationUpdates X
  live := bootstrapRelationUpdates X

/-- The immutable birth-history delta is exactly M004's direct birth pair. -/
def recordInstructionUpdates {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (instruction : ResponseCoupledBirthInstruction next) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  instruction.parentChildBirthUpdates

/-- The current live delta is the complete relation-support part of M004.
`birthLapse` is not a relation update and remains owned downstream by C011. -/
def liveInstructionUpdates {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (instruction : ResponseCoupledBirthInstruction next) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  instruction.parentChildBirthUpdates ++
    instruction.ancestorBackreactionUpdates ++
    instruction.siblingBackreactionUpdates

/-- Apply one immutable M004 instruction without rewriting any earlier entry. -/
def applyInstruction {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    RecordLiveChannels X.grammar.branching where
  record := channels.record ++ recordInstructionUpdates instruction
  live := channels.live ++ liveInstructionUpdates instruction

/-- Bootstrap record and live are definitionally the same derived relation pair. -/
theorem bootstrap_record_eq_live (X : BootstrapState) :
    (bootstrapRecordLiveChannels X).record =
      (bootstrapRecordLiveChannels X).live := by
  rfl

/-- C008 preserves the previous record channel as an exact left prefix and
appends no M004 backreaction component to it. -/
theorem applyInstruction_record_eq {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    (applyInstruction channels instruction).record =
      channels.record ++ instruction.parentChildBirthUpdates := by
  rfl

/-- C008 preserves the previous live channel as an exact left prefix and
appends the complete M004 relation delta. -/
theorem applyInstruction_live_eq {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    (applyInstruction channels instruction).live =
      channels.live ++
        (instruction.parentChildBirthUpdates ++
          instruction.ancestorBackreactionUpdates ++
          instruction.siblingBackreactionUpdates) := by
  rfl

/-- Reflexivity for one M004 relation update under exact-fraction value
semantics. -/
theorem directedRelationUpdateSameValue_refl {b : BranchingParameter}
    (update : DirectedRelationUpdate b) :
    DirectedRelationUpdateSameValue update update where
  source_eq := rfl
  target_eq := rfl
  value_same := ExactFraction.sameValue_refl update.value

/-- Reflexivity of M004's list-level exact-value relation. -/
theorem directedRelationUpdatesSameValue_refl {b : BranchingParameter}
    (updates : List (DirectedRelationUpdate b)) :
    DirectedRelationUpdatesSameValue updates updates := by
  induction updates with
  | nil =>
      exact DirectedRelationUpdatesSameValue.nil
  | cons update rest ih =>
      exact DirectedRelationUpdatesSameValue.cons
        (directedRelationUpdateSameValue_refl update) ih

/-- M004 list-level value equality is stable under synchronized append. -/
theorem directedRelationUpdatesSameValue_append {b : BranchingParameter}
    {leftPrefix rightPrefix leftSuffix rightSuffix :
      List (DirectedRelationUpdate b)}
    (hPrefix : DirectedRelationUpdatesSameValue leftPrefix rightPrefix)
    (hSuffix : DirectedRelationUpdatesSameValue leftSuffix rightSuffix) :
    DirectedRelationUpdatesSameValue
      (leftPrefix ++ leftSuffix) (rightPrefix ++ rightSuffix) := by
  induction hPrefix with
  | nil =>
      exact hSuffix
  | cons hHead hTail ih =>
      exact DirectedRelationUpdatesSameValue.cons hHead ih

/-- The complete live delta respects M004 cross-representative equality. -/
theorem liveInstructionUpdates_respects_sameValue
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    {left right : ResponseCoupledBirthInstruction next}
    (hInstruction : BirthInstructionSameValue left right) :
    DirectedRelationUpdatesSameValue
      (liveInstructionUpdates left) (liveInstructionUpdates right) := by
  exact directedRelationUpdatesSameValue_append
    (directedRelationUpdatesSameValue_append
      hInstruction.parentChild_same hInstruction.ancestor_same)
    hInstruction.sibling_same

/-- Exact-value equality for both C008 channels. -/
structure RecordLiveChannelsSameValue {b : BranchingParameter}
    (left right : RecordLiveChannels b) : Prop where
  record_same : DirectedRelationUpdatesSameValue left.record right.record
  live_same : DirectedRelationUpdatesSameValue left.live right.live

/-- C008 channel value equality is reflexive. -/
theorem recordLiveChannelsSameValue_refl {b : BranchingParameter}
    (channels : RecordLiveChannels b) :
    RecordLiveChannelsSameValue channels channels where
  record_same := directedRelationUpdatesSameValue_refl channels.record
  live_same := directedRelationUpdatesSameValue_refl channels.live

/-- The C008 update depends only on the semantic exact values of the old
channels and the M004 instruction.  Hence distinct exact-fraction
representatives of one canonical M004 handoff cannot change the update result
modulo the same exact-value relation. -/
theorem applyInstruction_respects_sameValue
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
    {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next}
    (hChannels : RecordLiveChannelsSameValue leftChannels rightChannels)
    (hInstruction : BirthInstructionSameValue leftInstruction rightInstruction) :
    RecordLiveChannelsSameValue
      (applyInstruction leftChannels leftInstruction)
      (applyInstruction rightChannels rightInstruction) where
  record_same := directedRelationUpdatesSameValue_append
    hChannels.record_same hInstruction.parentChild_same
  live_same := directedRelationUpdatesSameValue_append
    hChannels.live_same
    (liveInstructionUpdates_respects_sameValue hInstruction)

/-- Core C008 contract: bootstrap coincidence, exact append semantics, and
representative-independent application.  It deliberately makes no C009/T002
claim about the full successor `ResponseCapableState`. -/
def RecordLiveResponseCoupledUpdateContract : Prop :=
  (∀ X : BootstrapState,
    (bootstrapRecordLiveChannels X).record =
      (bootstrapRecordLiveChannels X).live) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      (channels : RecordLiveChannels X.grammar.branching)
      (instruction : ResponseCoupledBirthInstruction next),
      (applyInstruction channels instruction).record =
        channels.record ++ instruction.parentChildBirthUpdates ∧
      (applyInstruction channels instruction).live =
        channels.live ++
          (instruction.parentChildBirthUpdates ++
            instruction.ancestorBackreactionUpdates ++
            instruction.siblingBackreactionUpdates)) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
      {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next},
      RecordLiveChannelsSameValue leftChannels rightChannels →
      BirthInstructionSameValue leftInstruction rightInstruction →
      RecordLiveChannelsSameValue
        (applyInstruction leftChannels leftInstruction)
        (applyInstruction rightChannels rightInstruction))

/-- The derived C008 Core implementation inhabits its complete local contract. -/
theorem recordLiveResponseCoupledUpdateContract :
    RecordLiveResponseCoupledUpdateContract := by
  constructor
  · intro X
    exact bootstrap_record_eq_live X
  · constructor
    · intro X next channels instruction
      exact ⟨applyInstruction_record_eq channels instruction,
        applyInstruction_live_eq channels instruction⟩
    · intro X next leftChannels rightChannels leftInstruction rightInstruction
        hChannels hInstruction
      exact applyInstruction_respects_sameValue hChannels hInstruction

end RecordLiveResponseCoupledUpdate

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
