import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S02_C016_ImmutableRecordChannel
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S03_C017_CurrentLiveChannel

/-!
Paper 1.4.4 / C009 — deterministic codomain-state assembly.

C009 is the first merge point between the recurrent C005 state and the two
C008-derived channel projections C016/C017.  It is deliberately an assembly
node rather than the recurrent-closure theorem.

For one C005 state `X`, its C004-selected next slot, coherent current C008
channels, and one M004-shaped instruction at that slot, C009 constructs the
unique raw codomain data:

* the born non-root prefix extended by exactly the selected child;
* the C016 immutable record projection after the instruction;
* the C017 current live projection after the instruction.

The input coherence predicate states that the pre-step C017 live channel is an
exact-value representation of the current ordered C005 conductance list.  This
predicate first makes sense at the C005/C017 merge and is therefore owned here.

C009 does *not* prove that the assembled raw codomain already inhabits the full
C005 `ResponseCapableState` schema.  Preservation of cutoff, initial-prefix,
conductance support/positivity/ordered-pair uniqueness and parent backbone is
T002.  If T002 needs missing supporting closure lemmas, they must be added at
their semantic owner (C004/C005/M004/etc.), not hidden inside C009.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB
open RecordLiveResponseCoupledUpdate

namespace CodomainStateX

/-- Exact C005↔C017 handoff coherence at the assembly boundary.  No new
conductance value is computed: each C005 rational conductance is merely viewed
through C008's already-defined exact-fraction representation map. -/
def StateChannelCoherent (X : ResponseCapableState)
    (channels : RecordLiveChannels X.grammar.branching) : Prop :=
  DirectedRelationUpdatesSameValue
    (CurrentLiveChannel.liveChannel channels)
    (X.conductances.map directedConductanceAsUpdate)

/-- Proof-bearing C009 input.  The next child is already selected by C004 and
`instruction` is typed at exactly that slot. -/
structure CodomainAssemblyInput (X : ResponseCapableState)
    (next : NextOpenSlot X) where
  channels : RecordLiveChannels X.grammar.branching
  instruction : ResponseCoupledBirthInstruction next
  live_coherent : StateChannelCoherent X channels

/-- Raw deterministic codomain data.  Grammar and schedule are inherited from
`X`; T002 later proves that these data re-enter the complete C005 schema. -/
structure CodomainStateData (X : ResponseCapableState)
    (next : NextOpenSlot X) where
  schedule : CanonicalBirthSchedule
  bornNonRoot : List (ProvenanceAddress X.grammar.branching)
  record : List (DirectedRelationUpdate X.grammar.branching)
  live : List (DirectedRelationUpdate X.grammar.branching)

/-- The unique C009 assembly: one child append plus the already-closed C016 and
C017 post-instruction projections. -/
def assemble {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : CodomainAssemblyInput X next) : CodomainStateData X next where
  schedule := X.schedule
  bornNonRoot := X.bornNonRoot ++ [next.val]
  record := ImmutableRecordChannel.afterInstruction input.channels input.instruction
  live := CurrentLiveChannel.afterInstruction input.channels input.instruction

/-- C009 inherits the canonical schedule literally; schedule advancement/event-time
semantics remain downstream. -/
theorem assemble_schedule_eq {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : CodomainAssemblyInput X next) :
    (assemble input).schedule = X.schedule := by
  rfl

/-- C009 changes the born carrier only by appending the selected C004 child. -/
theorem assemble_bornNonRoot_eq {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : CodomainAssemblyInput X next) :
    (assemble input).bornNonRoot = X.bornNonRoot ++ [next.val] := by
  rfl

/-- The assembled record component is exactly C016; C009 defines no second
record update law. -/
theorem assemble_record_eq_c016 {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : CodomainAssemblyInput X next) :
    (assemble input).record =
      ImmutableRecordChannel.afterInstruction input.channels input.instruction := by
  rfl

/-- The assembled live component is exactly C017; C009 defines no second live
update law. -/
theorem assemble_live_eq_c017 {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : CodomainAssemblyInput X next) :
    (assemble input).live =
      CurrentLiveChannel.afterInstruction input.channels input.instruction := by
  rfl

/-- Semantic exact-value equality for two raw C009 codomain assemblies.  The
born prefix is literal data; record/live values are compared by M004/C008
fraction-value equality. -/
structure CodomainStateDataSameValue {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (left right : CodomainStateData X next) : Prop where
  schedule_eq : left.schedule = right.schedule
  born_eq : left.bornNonRoot = right.bornNonRoot
  record_same : DirectedRelationUpdatesSameValue left.record right.record
  live_same : DirectedRelationUpdatesSameValue left.live right.live

/-- C009 adds no representative dependence beyond the already-proved C016/C017
channels. -/
theorem assemble_respects_sameValue
    {X : ResponseCapableState} {next : NextOpenSlot X}
    {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
    {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next}
    (leftCoherent : StateChannelCoherent X leftChannels)
    (rightCoherent : StateChannelCoherent X rightChannels)
    (hChannels : RecordLiveChannelsSameValue leftChannels rightChannels)
    (hInstruction : BirthInstructionSameValue leftInstruction rightInstruction) :
    CodomainStateDataSameValue
      (assemble ({ channels := leftChannels,
                   instruction := leftInstruction,
                   live_coherent := leftCoherent } : CodomainAssemblyInput X next))
      (assemble ({ channels := rightChannels,
                   instruction := rightInstruction,
                   live_coherent := rightCoherent } : CodomainAssemblyInput X next)) := by
  exact {
    schedule_eq := rfl
    born_eq := rfl
    record_same := ImmutableRecordChannel.afterInstruction_respects_sameValue
      hChannels hInstruction
    live_same := CurrentLiveChannel.afterInstruction_respects_sameValue
      hChannels hInstruction }

/-- Extensional specification of the deterministic C009 output for one fixed
proof-bearing input. -/
def IsCodomainAssembly {X : ResponseCapableState} {next : NextOpenSlot X}
    (input : CodomainAssemblyInput X next)
    (output : CodomainStateData X next) : Prop :=
  output = assemble input

/-- One fixed admissible C009 input has exactly one raw codomain assembly. -/
theorem codomainAssembly_existsUnique {X : ResponseCapableState}
    {next : NextOpenSlot X} (input : CodomainAssemblyInput X next) :
    ∃ output : CodomainStateData X next,
      IsCodomainAssembly input output ∧
      ∀ other : CodomainStateData X next, IsCodomainAssembly input other → other = output := by
  refine ⟨assemble input, rfl, ?_⟩
  intro other hOther
  exact hOther

/-- Complete C009 contract: exact component assembly, semantic representative
independence, and deterministic uniqueness.  It contains no T002 schema-closure
claim. -/
def CodomainStateAssemblyContract : Prop :=
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      (input : CodomainAssemblyInput X next),
      (assemble input).schedule = X.schedule ∧
      (assemble input).bornNonRoot = X.bornNonRoot ++ [next.val] ∧
      (assemble input).record =
        ImmutableRecordChannel.afterInstruction input.channels input.instruction ∧
      (assemble input).live =
        CurrentLiveChannel.afterInstruction input.channels input.instruction) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      {leftChannels rightChannels : RecordLiveChannels X.grammar.branching}
      {leftInstruction rightInstruction : ResponseCoupledBirthInstruction next}
      (leftCoherent : StateChannelCoherent X leftChannels)
      (rightCoherent : StateChannelCoherent X rightChannels),
      RecordLiveChannelsSameValue leftChannels rightChannels →
      BirthInstructionSameValue leftInstruction rightInstruction →
      CodomainStateDataSameValue
        (assemble ({ channels := leftChannels,
                     instruction := leftInstruction,
                     live_coherent := leftCoherent } : CodomainAssemblyInput X next))
        (assemble ({ channels := rightChannels,
                     instruction := rightInstruction,
                     live_coherent := rightCoherent } : CodomainAssemblyInput X next))) ∧
  (∀ {X : ResponseCapableState} {next : NextOpenSlot X}
      (input : CodomainAssemblyInput X next),
      ∃ output : CodomainStateData X next,
        IsCodomainAssembly input output ∧
        ∀ other : CodomainStateData X next, IsCodomainAssembly input other → other = output)

/-- The derived implementation inhabits the complete local C009 contract. -/
theorem codomainStateAssemblyContract : CodomainStateAssemblyContract := by
  constructor
  · intro X next input
    exact ⟨assemble_schedule_eq input,
      assemble_bornNonRoot_eq input,
      assemble_record_eq_c016 input,
      assemble_live_eq_c017 input⟩
  · constructor
    · intro X next leftChannels rightChannels leftInstruction rightInstruction
        leftCoherent rightCoherent hChannels hInstruction
      exact assemble_respects_sameValue leftCoherent rightCoherent
        hChannels hInstruction
    · intro X next input
      exact codomainAssembly_existsUnique input

end CodomainStateX

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
