import CNNAProofs.M003M004.S02_CanonicalM004ClosureAndHandoff
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.S01_C008_RecordLiveResponseCoupledUpdate

/-!
C008 proof facade — canonical M004 handoff to record/live update.

The Core C008 transformation is total once an immutable M004 instruction is
supplied.  This proof facade closes the dependency edge M004 -> C008: every
canonical state-directed realization supplies such an instruction, and any two
canonical representatives induce the same C008 record/live result modulo C006
exact-fraction value equality.
-/

namespace CNNAProofs.C008

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.NextOpenProvenanceSlot
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.InterBirthDirectedResponse
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.ResponseCoupledBirthLawBirthlawB
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S04_RecordLiveUpdateBackreactionChannelsAndFiniteClosure.RecordLiveResponseCoupledUpdate
open CNNAProofs.M003M004

/-- Canonical C008 closure for one current state, slot realization, and existing
record/live channel pair. -/
structure CanonicalRecordLiveUpdateClosure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (channels : RecordLiveChannels X.grammar.branching) : Prop where
  updateExists :
    ∃ instruction : ResponseCoupledBirthInstruction next,
      ∃ output : RecordLiveChannels X.grammar.branching,
        IsCanonicalBirthInstructionHandoff realization instruction ∧
        output = applyInstruction channels instruction
  representativeIndependent :
    ∀ (left right : ResponseCoupledBirthInstruction next),
      IsCanonicalBirthInstructionHandoff realization left →
      IsCanonicalBirthInstructionHandoff realization right →
      RecordLiveChannelsSameValue
        (applyInstruction channels left)
        (applyInstruction channels right)

/-- M004's verified immutable handoff closes C008 existence and semantic
representative-independence without adding another growth parameter. -/
theorem canonicalRecordLiveUpdateClosure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (channels : RecordLiveChannels X.grammar.branching) :
    CanonicalRecordLiveUpdateClosure realization channels := by
  refine {
    updateExists := ?_
    representativeIndependent := ?_ }
  · obtain ⟨instruction, hInstruction⟩ :=
      canonicalBirthInstructionHandoff_exists realization
    exact ⟨instruction, applyInstruction channels instruction,
      hInstruction, rfl⟩
  · intro left right hLeft hRight
    have hInstruction : BirthInstructionSameValue left right :=
      canonicalBirthInstructionHandoff_sameValue realization hLeft hRight
    exact applyInstruction_respects_sameValue
      (recordLiveChannelsSameValue_refl channels) hInstruction

/-- Public C008 proof contract.  Literal equality of exact-fraction
representatives is intentionally not claimed; M004 itself guarantees only
semantic exact-value equivalence across representatives. -/
def CanonicalRecordLiveUpdateContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (channels : RecordLiveChannels X.grammar.branching),
      CanonicalRecordLiveUpdateClosure realization channels

/-- The canonical M004 -> C008 handoff contract is inhabited. -/
theorem canonicalRecordLiveUpdateContract :
    CanonicalRecordLiveUpdateContract := by
  intro X next realization channels
  exact canonicalRecordLiveUpdateClosure realization channels

end CNNAProofs.C008
