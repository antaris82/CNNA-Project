import CNNAProofs.C016C017
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S04_C009_CodomainStateX

/-!
C009 proof facade — deterministic codomain-state assembly.

This facade certifies only the C009 assembly boundary.  It deliberately does
not claim the T002 theorem that the raw output is again a C005
`ResponseCapableState`.
-/

namespace CNNAProofs.C009

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.CodomainStateX
open CNNAProofs.C016C017

/-- Proof-facing closure of C009 together with its already-verified C016/C017
handoff. -/
structure CanonicalCodomainStateAssemblyClosure : Prop where
  channel_projection_contract : CanonicalRecordLiveChannelProjectionContract
  core_contract : CodomainStateAssemblyContract

/-- C009 is closed by the C016/C017 projection handoff and its Core assembly
contract. -/
theorem canonicalCodomainStateAssemblyClosure :
    CanonicalCodomainStateAssemblyClosure where
  channel_projection_contract := canonicalRecordLiveChannelProjectionContract
  core_contract := codomainStateAssemblyContract

/-- Public C009 contract used by T002. -/
def CanonicalCodomainStateAssemblyContract : Prop :=
  CanonicalCodomainStateAssemblyClosure

/-- The canonical C009 construction inhabits its public T002-facing contract. -/
theorem canonicalCodomainStateAssemblyContract :
    CanonicalCodomainStateAssemblyContract :=
  canonicalCodomainStateAssemblyClosure

end CNNAProofs.C009
