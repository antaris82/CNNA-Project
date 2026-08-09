import Init

/-!
Paper 1.3.7 / O001 — IST response-independent legacy-channel obstruction.

O001 records an implementation obstruction in the bound legacy growth path.
The original gate exposed rank, forward, and backward channels.  The M004
Tier-C review showed that the same path also contains response-independent
node-load scalars, nonlinear mode transforms, fixed backreaction scales,
additive unit baselines, and explicit geometric attenuation.  None is supplied
by the measured C007 response or the M003 steering value.

This is not a theorem that arbitrary growth laws cannot contain such terms.
Lean makes the refactor boundary explicit and falsifiable.  A candidate tuple
carries the intended M004 variables `state`, `slot`, `response`, and `steering`
together with one Boolean flag for every forbidden legacy mechanism class.
Acceptance requires equality with the all-false witness.  Every individual
active channel is therefore formally rejectable, while the acceptance
constructor preserves exactly the four intended variables and drops the
obstruction record.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

namespace IstResponseIndependentDirectedBiasObstruction

/-- Presence of every response-independent legacy mechanism excluded from the
active derived-only M004 interface.  The flags record mechanism presence only;
O001 owns no numerical weights. -/
structure IndependentDirectedBiasPresence where
  rank : Bool
  forward : Bool
  backward : Bool
  nodeLoadScalar : Bool
  nonlinearMode : Bool
  backreactionScale : Bool
  additiveBaseline : Bool
  geometricAttenuation : Bool

/-- The unique all-false declaration accepted by O001. -/
def noIndependentDirectedBias : IndependentDirectedBiasPresence where
  rank := false
  forward := false
  backward := false
  nodeLoadScalar := false
  nonlinearMode := false
  backreactionScale := false
  additiveBaseline := false
  geometricAttenuation := false

/-- Historical witness for the original three-channel audit. -/
def legacyRankForwardBackwardBias : IndependentDirectedBiasPresence where
  rank := true
  forward := true
  backward := true
  nodeLoadScalar := false
  nonlinearMode := false
  backreactionScale := false
  additiveBaseline := false
  geometricAttenuation := false

/-- Full witness matching the response-independent mechanisms found in the
bound legacy growth implementation. -/
def legacyResponseIndependentChannels : IndependentDirectedBiasPresence where
  rank := true
  forward := true
  backward := true
  nodeLoadScalar := true
  nonlinearMode := true
  backreactionScale := true
  additiveBaseline := true
  geometricAttenuation := true

/-- Removal is exact equality with the unique all-false presence record. -/
def IsRemoved (bias : IndependentDirectedBiasPresence) : Prop :=
  bias = noIndependentDirectedBias

/-- Candidate dependencies before the O001 refactor gate. -/
structure CandidateGrowthLawInputs
    (State Slot Response Steering : Type) where
  state : State
  slot : Slot
  response : Response
  steering : Steering
  independentBias : IndependentDirectedBiasPresence

/-- The downstream M004 dependency tuple after O001 has removed every extra
legacy channel. -/
structure BiasFreeGrowthLawInputs
    (State Slot Response Steering : Type) where
  state : State
  slot : Slot
  response : Response
  steering : Steering

/-- A candidate passes exactly when the complete obstruction record is the
all-false declaration. -/
def IsAdmissible
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering) : Prop :=
  IsRemoved candidate.independentBias

/-- Construct the bias-free dependency tuple. -/
def acceptBiasFree
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (_ : IsAdmissible candidate) :
    BiasFreeGrowthLawInputs State Slot Response Steering where
  state := candidate.state
  slot := candidate.slot
  response := candidate.response
  steering := candidate.steering

/-- Acceptance preserves the C005/M004 state variable exactly. -/
theorem accepted_preserves_state
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (h : IsAdmissible candidate) :
    (acceptBiasFree candidate h).state = candidate.state := rfl

/-- Acceptance preserves the C004 next-slot variable exactly. -/
theorem accepted_preserves_slot
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (h : IsAdmissible candidate) :
    (acceptBiasFree candidate h).slot = candidate.slot := rfl

/-- Acceptance preserves the measured C007 response exactly. -/
theorem accepted_preserves_response
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (h : IsAdmissible candidate) :
    (acceptBiasFree candidate h).response = candidate.response := rfl

/-- Acceptance preserves the response-derived M003 steering value exactly. -/
theorem accepted_preserves_steering
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (h : IsAdmissible candidate) :
    (acceptBiasFree candidate h).steering = candidate.steering := rfl

private theorem true_ne_false : true ≠ false := by
  intro h
  cases h

/-- Any active independent rank channel blocks acceptance. -/
theorem rank_bias_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hRank : candidate.independentBias.rank ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.rank hAccepted
  exact hRank hField

/-- Any active independent forward channel blocks acceptance. -/
theorem forward_bias_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hForward : candidate.independentBias.forward ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.forward hAccepted
  exact hForward hField

/-- Any active independent backward channel blocks acceptance. -/
theorem backward_bias_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hBackward : candidate.independentBias.backward ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.backward hAccepted
  exact hBackward hField

/-- Any response-independent node-load scalar blocks acceptance. -/
theorem node_load_scalar_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hNodeLoad : candidate.independentBias.nodeLoadScalar ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.nodeLoadScalar hAccepted
  exact hNodeLoad hField

/-- Any nonlinear legacy mode transform blocks acceptance. -/
theorem nonlinear_mode_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hMode : candidate.independentBias.nonlinearMode ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.nonlinearMode hAccepted
  exact hMode hField

/-- Any fixed ancestor/sibling backreaction scale blocks acceptance. -/
theorem backreaction_scale_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hScale : candidate.independentBias.backreactionScale ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.backreactionScale hAccepted
  exact hScale hField

/-- Any additive response-independent baseline blocks acceptance. -/
theorem additive_baseline_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hBaseline : candidate.independentBias.additiveBaseline ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.additiveBaseline hAccepted
  exact hBaseline hField

/-- Any explicit depth/rank-distance attenuation blocks acceptance. -/
theorem geometric_attenuation_blocks_acceptance
    {State Slot Response Steering : Type}
    (candidate : CandidateGrowthLawInputs State Slot Response Steering)
    (hAttenuation : candidate.independentBias.geometricAttenuation ≠ false) :
    ¬ IsAdmissible candidate := by
  intro hAccepted
  have hField := congrArg IndependentDirectedBiasPresence.geometricAttenuation hAccepted
  exact hAttenuation hField

/-- The full legacy channel-presence witness is not removed. -/
theorem legacy_channels_not_removed :
    ¬ IsRemoved legacyResponseIndependentChannels := by
  intro hRemoved
  have hRank := congrArg IndependentDirectedBiasPresence.rank hRemoved
  exact true_ne_false hRank

/-- A candidate carrying the full legacy witness cannot cross the O001 gate. -/
theorem legacy_candidate_not_admissible
    {State Slot Response Steering : Type}
    (state : State) (slot : Slot) (response : Response) (steering : Steering) :
    ¬ IsAdmissible
      ({ state := state
         slot := slot
         response := response
         steering := steering
         independentBias := legacyResponseIndependentChannels } :
        CandidateGrowthLawInputs State Slot Response Steering) := by
  exact rank_bias_blocks_acceptance _ true_ne_false

end IstResponseIndependentDirectedBiasObstruction

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
