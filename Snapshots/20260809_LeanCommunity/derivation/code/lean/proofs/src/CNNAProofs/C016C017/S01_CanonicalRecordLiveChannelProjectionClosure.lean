import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S02_C016_ImmutableRecordChannel
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S03_C017_CurrentLiveChannel

/-!
C016/C017 proof facade — canonical record/live channel projections.

These are thin proof-facing closures over the Core constructions.  No new
response law or recurrent successor is introduced here.  The purpose is to
make the two downstream construction boundaries independently auditable while
keeping routine projection lemmas local to their owners.
-/

namespace CNNAProofs.C016C017

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.ImmutableRecordChannel
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.CurrentLiveChannel

/-- Proof-facing closure of the C016 immutable-record construction. -/
structure CanonicalImmutableRecordChannelClosure : Prop where
  core_contract : ImmutableRecordChannelContract

/-- C016 is closed directly by its Core contract. -/
theorem canonicalImmutableRecordChannelClosure :
    CanonicalImmutableRecordChannelClosure where
  core_contract := immutableRecordChannelContract

/-- Proof-facing closure of the C017 current-live construction. -/
structure CanonicalCurrentLiveChannelClosure : Prop where
  core_contract : CurrentLiveChannelContract

/-- C017 is closed directly by its Core contract. -/
theorem canonicalCurrentLiveChannelClosure :
    CanonicalCurrentLiveChannelClosure where
  core_contract := currentLiveChannelContract

/-- Combined handoff required by C009: both C008 channel projections are closed
without identifying record and live after the bootstrap. -/
def CanonicalRecordLiveChannelProjectionContract : Prop :=
  CanonicalImmutableRecordChannelClosure ∧ CanonicalCurrentLiveChannelClosure

/-- C016 and C017 jointly inhabit their C009-facing projection contract. -/
theorem canonicalRecordLiveChannelProjectionContract :
    CanonicalRecordLiveChannelProjectionContract := by
  exact ⟨canonicalImmutableRecordChannelClosure,
    canonicalCurrentLiveChannelClosure⟩

end CNNAProofs.C016C017
