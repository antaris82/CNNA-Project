import CNNAProofs.M003M004.S02_CanonicalM004ClosureAndHandoff
import CNNAProofs.C009
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S06A_C007_StateDirectedBlockRealizationClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S05_T002_RecurrentStateClosureTheorem

/-!
T002 proof facade — canonical recurrent state closure.

The Core theorem is proof-bearing.  This facade closes the two quantities that
must not become public free inputs: C007 now constructs the canonical rational
state-directed block realization itself, and the already-closed M003/M004 chain
then supplies the exact positive response-steering pair.  The recurrent input
that remains explicit is the derived record/live context together with its
C005↔C017 live coherence; the immutable record history is not recoverable from
the C005 state alone.
-/

namespace CNNAProofs.T002

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.InterBirthDirectedResponse
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.CanonicalResponseSteeringFunctionalSigmaBRnS
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.RecordLiveResponseCoupledUpdate
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.CodomainStateX
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.RecurrentStateClosureTheorem
open CNNAProofs.M003M004
open CNNAProofs.P001

/-- The C007 origin closure plus canonical M003/M004 closure and one coherent
derived channel context supply a proof-bearing Core T002 input. -/
theorem canonicalRecurrentStepInput_exists
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (hCoherent : StateChannelCoherent X channels) :
    ∃ input : RecurrentStepInput X next,
      input.channels = channels ∧
      IsCanonicalBirthInstructionHandoff
        (canonicalStateDirectedBlockRealization next) (instruction input) := by
  let realization := canonicalStateDirectedBlockRealization next
  let m004 := canonicalM004Closure realization
  obtain ⟨response, value, hPair⟩ := m004.m003Closure.responseSteeringExists
  have hPositive : PositiveSteering value :=
    m004.m003Closure.everySteeringPositive response value hPair
  let input : RecurrentStepInput X next := {
    channels := channels
    live_coherent := hCoherent
    response := response
    value := value
    pair := hPair
    positive := hPositive }
  refine ⟨input, rfl, ?_⟩
  refine ⟨response, value, hPair, ?_⟩
  exact ⟨hPositive, rfl⟩

/-- Canonical T002 closure exists without an externally supplied C007
realization, response representative, or positivity witness. -/
theorem canonicalRecurrentStateClosure_exists
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (hCoherent : StateChannelCoherent X channels) :
    ∃ input : RecurrentStepInput X next,
      input.channels = channels ∧
      IsCanonicalBirthInstructionHandoff
        (canonicalStateDirectedBlockRealization next) (instruction input) ∧
      RecurrentStateClosure input := by
  obtain ⟨input, hChannels, hCanonical⟩ :=
    canonicalRecurrentStepInput_exists (next := next) channels hCoherent
  exact ⟨input, hChannels, hCanonical, recurrentStateClosure input⟩

/-- Public load-bearing T002 closure for one admissible recurrent configuration:
a C005 state, its selected C004 slot, and the derived record/live context whose
live channel represents the current C005 conductances.  The facade remains
Prop-valued: C007 data are consumed canonically and are not re-exported as a
downstream data field. -/
structure CanonicalRecurrentStateClosure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (hCoherent : StateChannelCoherent X channels) : Prop where
  c007Canonical :
    ∃ realization : StateDirectedBlockRealization X next,
      realization = canonicalStateDirectedBlockRealization next
  m004Closure :
    CanonicalM004Closure (canonicalStateDirectedBlockRealization next)
  inputExists :
    ∃ input : RecurrentStepInput X next,
      input.channels = channels ∧
      IsCanonicalBirthInstructionHandoff
        (canonicalStateDirectedBlockRealization next) (instruction input) ∧
      RecurrentStateClosure input

/-- Every admissible recurrent configuration satisfies the complete one-step
T002 closure. -/
theorem canonicalRecurrentStateClosure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (hCoherent : StateChannelCoherent X channels) :
    CanonicalRecurrentStateClosure (next := next) channels hCoherent := by
  refine {
    c007Canonical := ⟨canonicalStateDirectedBlockRealization next, rfl⟩
    m004Closure := canonicalM004Closure (canonicalStateDirectedBlockRealization next)
    inputExists := ?_ }
  obtain ⟨input, hChannels, hCanonical, hClosure⟩ :=
    canonicalRecurrentStateClosure_exists (next := next) channels hCoherent
  exact ⟨input, hChannels, hCanonical, hClosure⟩

/-- Public T002 contract.  Record/live history is part of the recurrent state
context; the C007 numerical realization and response/steering witnesses are
fully derived. -/
def CanonicalRecurrentStateClosureContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (channels : RecordLiveChannels X.grammar.branching)
    (hCoherent : StateChannelCoherent X channels),
      CanonicalRecurrentStateClosure (next := next) channels hCoherent

/-- The canonical recurrent construction inhabits the public T002 contract. -/
theorem canonicalRecurrentStateClosureContract :
    CanonicalRecurrentStateClosureContract := by
  intro X next channels hCoherent
  exact canonicalRecurrentStateClosure (next := next) channels hCoherent

end CNNAProofs.T002
