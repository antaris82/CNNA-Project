import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S01_C008_RecordLiveResponseCoupledUpdate

/-!
Paper 1.4.2 / C016 — immutable record channel.

C016 isolates the historical channel already constructed by C008.  Its local
immutability statement is deliberately one-step and structural: every C008
update preserves the complete previous record as a literal left prefix and
appends only the direct parent/newborn birth pair from the canonical M004
instruction.  No ancestor or sibling backreaction enters the record delta.

This is the strongest future-preservation statement available before C009/P005
construct a typed recurrent successor chain.  C016 therefore does not claim a
separate arbitrary-many-birth theorem; later future-invariance results must be
proved on the recurrent/projective carrier once that carrier exists.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB
open RecordLiveResponseCoupledUpdate

namespace ImmutableRecordChannel

/-- C016 projection: the birth-time provenance history carried by C008. -/
def recordChannel {b : BranchingParameter} (channels : RecordLiveChannels b) :
    List (DirectedRelationUpdate b) :=
  channels.record

/-- Record channel after applying one canonical M004 instruction through C008. -/
def afterInstruction {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  recordChannel (applyInstruction channels instruction)

/-- The exceptional bootstrap record is exactly C008's already-derived X₁ pair. -/
theorem bootstrap_recordChannel_eq (X : BootstrapState) :
    recordChannel (bootstrapRecordLiveChannels X) = bootstrapRelationUpdates X := by
  rfl

/-- One C008 step never rewrites old record data and appends only the direct
parent/newborn birth pair. -/
theorem afterInstruction_eq_append {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    afterInstruction channels instruction =
      recordChannel channels ++ instruction.parentChildBirthUpdates := by
  exact applyInstruction_record_eq channels instruction

/-- Local immutability as an explicit prefix witness.  This quantifies over an
arbitrary pre-existing record channel, so every admissible C008 step preserves
all previously stored birth-time entries exactly. -/
theorem previousRecord_isLeftPrefix {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    ∃ suffix,
      afterInstruction channels instruction = recordChannel channels ++ suffix := by
  exact ⟨instruction.parentChildBirthUpdates,
    afterInstruction_eq_append channels instruction⟩

/-- C016 inherits C008's exact-value representative independence. -/
theorem afterInstruction_respects_sameValue
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
    {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next}
    (hChannels : RecordLiveChannelsSameValue leftChannels rightChannels)
    (hInstruction : BirthInstructionSameValue leftInstruction rightInstruction) :
    DirectedRelationUpdatesSameValue
      (afterInstruction leftChannels leftInstruction)
      (afterInstruction rightChannels rightInstruction) := by
  exact (applyInstruction_respects_sameValue hChannels hInstruction).record_same

/-- Complete local C016 contract.  The contract is intentionally restricted to
the bootstrap base, one-step append-only immutability, and semantic
representative independence. -/
def ImmutableRecordChannelContract : Prop :=
  (∀ X : BootstrapState,
    recordChannel (bootstrapRecordLiveChannels X) = bootstrapRelationUpdates X) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      (channels : RecordLiveChannels X.grammar.branching)
      (instruction : ResponseCoupledBirthInstruction next),
      afterInstruction channels instruction =
        recordChannel channels ++ instruction.parentChildBirthUpdates ∧
      ∃ suffix,
        afterInstruction channels instruction = recordChannel channels ++ suffix) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
      {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next},
      RecordLiveChannelsSameValue leftChannels rightChannels →
      BirthInstructionSameValue leftInstruction rightInstruction →
      DirectedRelationUpdatesSameValue
        (afterInstruction leftChannels leftInstruction)
        (afterInstruction rightChannels rightInstruction))

/-- The derived C016 projection inhabits its complete local contract. -/
theorem immutableRecordChannelContract : ImmutableRecordChannelContract := by
  constructor
  · intro X
    exact bootstrap_recordChannel_eq X
  · constructor
    · intro X next channels instruction
      exact ⟨afterInstruction_eq_append channels instruction,
        previousRecord_isLeftPrefix channels instruction⟩
    · intro X next leftChannels rightChannels leftInstruction rightInstruction
        hChannels hInstruction
      exact afterInstruction_respects_sameValue hChannels hInstruction

end ImmutableRecordChannel

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
