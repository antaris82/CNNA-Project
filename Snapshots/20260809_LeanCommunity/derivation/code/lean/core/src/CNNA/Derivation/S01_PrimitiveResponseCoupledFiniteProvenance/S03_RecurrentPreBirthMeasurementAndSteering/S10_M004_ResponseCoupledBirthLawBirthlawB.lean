import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S07_O001_IstResponseIndependentDirectedBiasObstruction
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S09_M003_CanonicalResponseSteeringFunctionalSigmaBRnS

/-!
Paper 1.3.10 / M004 — response-coupled birth law `B_b`.

M004 consumes the recurrent C005 state, its C004 slot, the actual exact C007
response, and the M003 steering value. O001 removes every independent rank,
forward, and backward bias before this node. Provenance fixes only the support
of the birth instruction.

The canonical candidate is the parameter-free structured lift.  Algebraically,
the same exact nonnegative value is transported to

* the two direct parent/newborn birth relations;
* the live newborn-to-strict-ancestor backreaction;
* both live orientations between the newborn and each earlier sibling; and
* the response-derived birth lapse.

Zero belongs to the pure lift domain and gives zero on every response-derived
channel.  It does not belong to the active recurrent birth domain, because C005
stores only strictly positive directed conductances.  M004 therefore keeps a
`PositiveSteering` proof argument at the mathlib-free Core boundary.  The proof
package derives that witness for every canonical C007/M003 pair, proves the
active instruction exists uniquely, and exposes a representative-independent
handoff for the next state-update node.

There is no separate newborn coefficient, birth-counter update, numerical rank,
rank distance, depth attenuation, baseline, fitted sign, free coefficient,
clipping, logarithm, saturation, or legacy node-load scalar. M004 returns an
immutable instruction and does not create C008 record/live successor states.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open NextOpenProvenanceSlot
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open InterBirthDirectedResponse
open IstResponseIndependentDirectedBiasObstruction
open CanonicalResponseSteeringFunctionalSigmaBRnS

namespace ResponseCoupledBirthLawBirthlawB

/-- Algebraic domain of the pure lift: zero or a strictly positive numerator.
The active birth law below uses only the positive branch. -/
def NonnegativeLiftValue (value : ExactFraction) : Prop :=
  value.num = 0 ∨ PositiveSteering value

/-- One directed relation instruction. C008 later owns its application. -/
structure DirectedRelationUpdate (b : BranchingParameter) where
  source : ProvenanceAddress b
  target : ProvenanceAddress b
  value : ExactFraction

/-- Complete immutable M004 channel assignment. -/
structure ResponseCoupledBirthInstruction {X : ResponseCapableState}
    (next : NextOpenSlot X) where
  steeringValue : ExactFraction
  parentChildBirthUpdates : List (DirectedRelationUpdate X.grammar.branching)
  ancestorBackreactionUpdates : List (DirectedRelationUpdate X.grammar.branching)
  siblingBackreactionUpdates : List (DirectedRelationUpdate X.grammar.branching)
  birthLapse : ExactFraction

/-- M001's root-to-parent chain with the direct parent removed. The parent is
already handled by the two parent/child updates. -/
def strictAncestorPorts {X : ResponseCapableState} (next : NextOpenSlot X) :
    List (ProvenanceAddress X.grammar.branching) :=
  (causalPredecessorPorts next).dropLast

/-- One relation carrying the M003 value without another scalar operation. -/
def directRelationUpdate {b : BranchingParameter}
    (source target : ProvenanceAddress b) (value : ExactFraction) :
    DirectedRelationUpdate b where
  source := source
  target := target
  value := value

/-- The two direct parent/newborn birth relations. -/
def parentChildUpdates {X : ResponseCapableState} (next : NextOpenSlot X)
    (value : ExactFraction) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  [ directRelationUpdate (parentAddress next) next.val value,
    directRelationUpdate next.val (parentAddress next) value ]

/-- Live newborn-to-strict-ancestor backreaction. -/
def ancestorBackreactionUpdates {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  (strictAncestorPorts next).map fun ancestor =>
    directRelationUpdate next.val ancestor value

/-- Two live orientations for each already-born earlier sibling. -/
def siblingBackreactionAux {b : BranchingParameter}
    (child : ProvenanceAddress b) :
    List (ProvenanceAddress b) → ExactFraction →
      List (DirectedRelationUpdate b)
  | [], _ => []
  | sibling :: rest, value =>
      directRelationUpdate sibling child value ::
      directRelationUpdate child sibling value ::
      siblingBackreactionAux child rest value

/-- Live sibling support fixed by M001/C004; numeric ranks do not enter weights. -/
def siblingBackreactionUpdates {X : ResponseCapableState}
    (next : NextOpenSlot X) (value : ExactFraction) :
    List (DirectedRelationUpdate X.grammar.branching) :=
  siblingBackreactionAux next.val (olderSiblingPorts next) value

/-- Pure structured lift `B_b(sigma)`. Provenance determines support only. -/
def directResponseLift {X : ResponseCapableState} (next : NextOpenSlot X)
    (value : ExactFraction) (_hNonnegative : NonnegativeLiftValue value) :
    ResponseCoupledBirthInstruction next where
  steeringValue := value
  parentChildBirthUpdates := parentChildUpdates next value
  ancestorBackreactionUpdates := ancestorBackreactionUpdates next value
  siblingBackreactionUpdates := siblingBackreactionUpdates next value
  birthLapse := value

/-- O001-facing candidate tuple. The three forbidden channels are explicitly
absent before the M004 constructor is used. -/
def candidateInputs {X : ResponseCapableState} (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction) :
    CandidateGrowthLawInputs ResponseCapableState (NextOpenSlot X)
      (ExactFractionMatrix (boundary next).length (boundary next).length)
      ExactFraction where
  state := X
  slot := next
  response := lambda
  steering := value
  independentBias := noIndependentDirectedBias

/-- The canonical M004 dependency tuple passes O001. -/
theorem candidateInputs_admissible {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction) :
    IsAdmissible (candidateInputs next lambda value) := by
  rfl

/-- Explicit O001 handoff retaining only state, slot, response, and steering. -/
def biasFreeInputs {X : ResponseCapableState} (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction) :
    BiasFreeGrowthLawInputs ResponseCapableState (NextOpenSlot X)
      (ExactFractionMatrix (boundary next).length (boundary next).length)
      ExactFraction :=
  acceptBiasFree (candidateInputs next lambda value)
    (candidateInputs_admissible next lambda value)

/-- Canonical parameter-free response-coupled birth law.  The proof arguments
state the exact C007/M003 handoff and the strictly positive active C005 domain,
but add no output field.  The proof package supplies both arguments through the
closed canonical M003/M004 interface. -/
def birthLaw {X : ResponseCapableState} {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (_hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value) :
    ResponseCoupledBirthInstruction next :=
  directResponseLift next value (Or.inr hPositive)

/-- Extensional characterization for one fixed exact input representation. -/
def IsCanonicalBirthLaw {X : ResponseCapableState} {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value)
    (output : ResponseCoupledBirthInstruction next) : Prop :=
  output = birthLaw realization lambda value hPair hPositive

/-- Same endpoints and the same exact fraction value. -/
structure DirectedRelationUpdateSameValue {b : BranchingParameter}
    (left right : DirectedRelationUpdate b) : Prop where
  source_eq : left.source = right.source
  target_eq : left.target = right.target
  value_same : ExactFraction.SameValue left.value right.value

/-- Core-local pointwise relation for two directed-update lists.  It is
length-synchronous by construction and avoids adding a Mathlib list-relation
import to the Section-1 foundation. -/
inductive DirectedRelationUpdatesSameValue {b : BranchingParameter} :
    List (DirectedRelationUpdate b) →
      List (DirectedRelationUpdate b) → Prop where
  | nil : DirectedRelationUpdatesSameValue [] []
  | cons {left right : DirectedRelationUpdate b}
      {leftRest rightRest : List (DirectedRelationUpdate b)} :
      DirectedRelationUpdateSameValue left right →
      DirectedRelationUpdatesSameValue leftRest rightRest →
      DirectedRelationUpdatesSameValue
        (left :: leftRest) (right :: rightRest)

/-- Cross-representative equality for the complete birth instruction. -/
structure BirthInstructionSameValue {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (left right : ResponseCoupledBirthInstruction next) : Prop where
  steering_same : ExactFraction.SameValue left.steeringValue right.steeringValue
  parentChild_same : DirectedRelationUpdatesSameValue
    left.parentChildBirthUpdates right.parentChildBirthUpdates
  ancestor_same : DirectedRelationUpdatesSameValue
    left.ancestorBackreactionUpdates right.ancestorBackreactionUpdates
  sibling_same : DirectedRelationUpdatesSameValue
    left.siblingBackreactionUpdates right.siblingBackreactionUpdates
  lapse_same : ExactFraction.SameValue left.birthLapse right.birthLapse

/-- A direct relation lift respects C006 exact-fraction value equality. -/
theorem directRelationUpdate_respects_sameValue {b : BranchingParameter}
    (source target : ProvenanceAddress b) {left right : ExactFraction}
    (hValue : ExactFraction.SameValue left right) :
    DirectedRelationUpdateSameValue
      (directRelationUpdate source target left)
      (directRelationUpdate source target right) where
  source_eq := rfl
  target_eq := rfl
  value_same := hValue

/-- Mapping one child to a fixed address list respects exact fraction values. -/
theorem ancestorAux_respects_sameValue {b : BranchingParameter}
    (child : ProvenanceAddress b) (addresses : List (ProvenanceAddress b))
    {left right : ExactFraction}
    (hValue : ExactFraction.SameValue left right) :
    DirectedRelationUpdatesSameValue
      (addresses.map fun target => directRelationUpdate child target left)
      (addresses.map fun target => directRelationUpdate child target right) := by
  induction addresses with
  | nil =>
      exact DirectedRelationUpdatesSameValue.nil
  | cons address rest ih =>
      exact DirectedRelationUpdatesSameValue.cons
        (directRelationUpdate_respects_sameValue child address hValue) ih

/-- The two-orientation sibling recursion respects exact fraction values. -/
theorem siblingAux_respects_sameValue {b : BranchingParameter}
    (child : ProvenanceAddress b) (siblings : List (ProvenanceAddress b))
    {left right : ExactFraction}
    (hValue : ExactFraction.SameValue left right) :
    DirectedRelationUpdatesSameValue
      (siblingBackreactionAux child siblings left)
      (siblingBackreactionAux child siblings right) := by
  induction siblings with
  | nil =>
      exact DirectedRelationUpdatesSameValue.nil
  | cons sibling rest ih =>
      exact DirectedRelationUpdatesSameValue.cons
        (directRelationUpdate_respects_sameValue sibling child hValue)
        (DirectedRelationUpdatesSameValue.cons
          (directRelationUpdate_respects_sameValue child sibling hValue) ih)

/-- The pure structured lift is independent of raw exact-fraction representatives. -/
theorem directResponseLift_respects_sameValue {X : ResponseCapableState}
    (next : NextOpenSlot X) {left right : ExactFraction}
    (hLeftNonnegative : NonnegativeLiftValue left)
    (hRightNonnegative : NonnegativeLiftValue right)
    (hValue : ExactFraction.SameValue left right) :
    BirthInstructionSameValue
      (directResponseLift next left hLeftNonnegative)
      (directResponseLift next right hRightNonnegative) := by
  exact {
    steering_same := hValue
    parentChild_same := DirectedRelationUpdatesSameValue.cons
      (directRelationUpdate_respects_sameValue
        (parentAddress next) next.val hValue)
      (DirectedRelationUpdatesSameValue.cons
        (directRelationUpdate_respects_sameValue
          next.val (parentAddress next) hValue)
        DirectedRelationUpdatesSameValue.nil)
    ancestor_same :=
      ancestorAux_respects_sameValue next.val (strictAncestorPorts next) hValue
    sibling_same :=
      siblingAux_respects_sameValue next.val (olderSiblingPorts next) hValue
    lapse_same := hValue }

/-- The complete canonical M004 instruction respects C006 value equality. -/
theorem birthLaw_respects_sameValue {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (leftRealization rightRealization : StateDirectedBlockRealization X next)
    (leftResponse rightResponse :
      ExactFractionMatrix (boundary next).length (boundary next).length)
    {leftValue rightValue : ExactFraction}
    (hLeftPair : IsResponseSteeringPair leftRealization leftResponse leftValue)
    (hRightPair : IsResponseSteeringPair rightRealization rightResponse rightValue)
    (hLeftPositive : PositiveSteering leftValue)
    (hRightPositive : PositiveSteering rightValue)
    (hValue : ExactFraction.SameValue leftValue rightValue) :
    BirthInstructionSameValue
      (birthLaw leftRealization leftResponse leftValue hLeftPair hLeftPositive)
      (birthLaw rightRealization rightResponse rightValue hRightPair hRightPositive) := by
  exact directResponseLift_respects_sameValue next
    (Or.inr hLeftPositive) (Or.inr hRightPositive) hValue

/-- The canonical constructor always supplies one M004 output on its exact domain. -/
theorem birthLaw_exists {X : ResponseCapableState} {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value) :
    ∃ output : ResponseCoupledBirthInstruction next,
      IsCanonicalBirthLaw realization lambda value hPair hPositive output := by
  refine ⟨birthLaw realization lambda value hPair hPositive, ?_⟩
  rfl

/-- For one fixed exact input representation, the M004 instruction is unique. -/
theorem birthLaw_unique {X : ResponseCapableState} {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value)
    {left right : ResponseCoupledBirthInstruction next}
    (hLeft : IsCanonicalBirthLaw realization lambda value hPair hPositive left)
    (hRight : IsCanonicalBirthLaw realization lambda value hPair hPositive right) :
    left = right := by
  exact hLeft.trans hRight.symm

/-- Two C007/M003 representatives for the same state-directed realization give
M004 instructions with identical support and exact scalar values. -/
theorem responseSteeringPairs_give_same_birthLaw
    {X : ResponseCapableState} {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (hDomain : InResponseDomain realization)
    (leftResponse rightResponse :
      ExactFractionMatrix (boundary next).length (boundary next).length)
    {leftValue rightValue : ExactFraction}
    (hLeftPair : IsResponseSteeringPair realization leftResponse leftValue)
    (hRightPair : IsResponseSteeringPair realization rightResponse rightValue)
    (hLeftPositive : PositiveSteering leftValue)
    (hRightPositive : PositiveSteering rightValue) :
    BirthInstructionSameValue
      (birthLaw realization leftResponse leftValue hLeftPair hLeftPositive)
      (birthLaw realization rightResponse rightValue hRightPair hRightPositive) := by
  exact birthLaw_respects_sameValue
    realization realization leftResponse rightResponse
    hLeftPair hRightPair hLeftPositive hRightPositive
    (responseSteeringPair_value_unique realization hDomain
      leftResponse rightResponse hLeftPair hRightPair)

/-- Parent/newborn relation data are exactly the direct lift of the M003 value. -/
theorem birthLaw_parentChild_eq_directLift {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value) :
    (birthLaw realization lambda value hPair hPositive).parentChildBirthUpdates =
      parentChildUpdates next value :=
  rfl

/-- The physical birth-lapse channel is the same direct response-derived scalar. -/
theorem birthLaw_lapse_eq_steering {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization lambda value)
    (hPositive : PositiveSteering value) :
    (birthLaw realization lambda value hPair hPositive).birthLapse = value :=
  rfl

/-- The explicit zero lift has zero lapse; all relation constructors receive the
same `ExactFraction.zero` argument by definition. -/
theorem directResponseLift_zero_lapse {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    (directResponseLift next ExactFraction.zero (Or.inl rfl)).birthLapse = ExactFraction.zero :=
  rfl

end ResponseCoupledBirthLawBirthlawB

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
