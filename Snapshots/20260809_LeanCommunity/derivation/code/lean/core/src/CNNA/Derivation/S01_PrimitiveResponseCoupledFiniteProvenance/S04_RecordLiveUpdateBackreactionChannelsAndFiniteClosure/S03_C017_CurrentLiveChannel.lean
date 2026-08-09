import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S01_C008_RecordLiveResponseCoupledUpdate

/-!
Paper 1.4.3 / C017 — current live channel.

C017 isolates C008's current relation channel.  At each response-coupled birth,
the previous live channel is retained as a literal left prefix and the complete
M004 relation delta is appended: direct parent/newborn birth relations, strict-
ancestor backreaction, and earlier-sibling backreaction.

C017 is a relation-channel construction, not yet a Schur/DtN response,
live-minus-record observable, or backreaction current.  Those derived
observables remain downstream (in particular C024).
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB
open RecordLiveResponseCoupledUpdate

namespace CurrentLiveChannel

/-- C017 projection: the current relation channel carried by C008. -/
def liveChannel {b : BranchingParameter} (channels : RecordLiveChannels b) :
    List (DirectedRelationUpdate b) :=
  channels.live

/-- Live channel after applying one canonical M004 instruction through C008. -/
def afterInstruction {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  liveChannel (applyInstruction channels instruction)

/-- At the exceptional bootstrap, live and record start from the same C008 X₁ pair. -/
theorem bootstrap_liveChannel_eq (X : BootstrapState) :
    liveChannel (bootstrapRecordLiveChannels X) = bootstrapRelationUpdates X := by
  rfl

/-- One C008 step appends exactly the complete M004 live relation delta. -/
theorem afterInstruction_eq_append {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    afterInstruction channels instruction =
      liveChannel channels ++
        (instruction.parentChildBirthUpdates ++
          instruction.ancestorBackreactionUpdates ++
          instruction.siblingBackreactionUpdates) := by
  exact applyInstruction_live_eq channels instruction

/-- The old live channel is retained exactly as a left prefix.  Unlike C016,
the appended suffix includes the derived backreaction components. -/
theorem previousLive_isLeftPrefix {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (instruction : ResponseCoupledBirthInstruction next) :
    ∃ suffix,
      afterInstruction channels instruction = liveChannel channels ++ suffix := by
  exact ⟨liveInstructionUpdates instruction,
    afterInstruction_eq_append channels instruction⟩

/-- C017 inherits C008's exact-value representative independence. -/
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
  exact (applyInstruction_respects_sameValue hChannels hInstruction).live_same

/-- Complete local C017 contract: bootstrap base, exact one-step current-live
append semantics, prefix preservation, and representative independence. -/
def CurrentLiveChannelContract : Prop :=
  (∀ X : BootstrapState,
    liveChannel (bootstrapRecordLiveChannels X) = bootstrapRelationUpdates X) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      (channels : RecordLiveChannels X.grammar.branching)
      (instruction : ResponseCoupledBirthInstruction next),
      afterInstruction channels instruction =
        liveChannel channels ++
          (instruction.parentChildBirthUpdates ++
            instruction.ancestorBackreactionUpdates ++
            instruction.siblingBackreactionUpdates) ∧
      ∃ suffix,
        afterInstruction channels instruction = liveChannel channels ++ suffix) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
      {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next},
      RecordLiveChannelsSameValue leftChannels rightChannels →
      BirthInstructionSameValue leftInstruction rightInstruction →
      DirectedRelationUpdatesSameValue
        (afterInstruction leftChannels leftInstruction)
        (afterInstruction rightChannels rightInstruction))

/-- The derived C017 projection inhabits its complete local contract. -/
theorem currentLiveChannelContract : CurrentLiveChannelContract := by
  constructor
  · intro X
    exact bootstrap_liveChannel_eq X
  · constructor
    · intro X next channels instruction
      exact ⟨afterInstruction_eq_append channels instruction,
        previousLive_isLeftPrefix channels instruction⟩
    · intro X next leftChannels rightChannels leftInstruction rightInstruction
        hChannels hInstruction
      exact afterInstruction_respects_sameValue hChannels hInstruction

end CurrentLiveChannel

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
