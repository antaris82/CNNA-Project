import CNNAProofs.M003M004.S01_CanonicalM003Closure

/-!
# M004 — canonical birth-law closure and immutable handoff

This module consumes the closed M003 interface and closes the active M004 law.
For every canonical state-directed realization it proves existence of an active
birth instruction, uniqueness for each exact response-steering pair, and exact
representative independence.  The public interface has no parent-index or
positivity argument.

`IsCanonicalBirthInstructionHandoff` is the immutable output boundary consumed
by the later C008 state update.  This module constructs and characterizes that
handoff but does not mutate record or live state.
-/

namespace CNNAProofs.M003M004

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open NextOpenProvenanceSlot
open InterBirthDirectedResponse
open CanonicalResponseSteeringFunctionalSigmaBRnS
open ResponseCoupledBirthLawBirthlawB
open CNNAProofs.P001

/-- Closed canonical M004 interface.  It consumes M003 closure and exposes the
active immutable birth instruction without proof-selection parameters. -/
structure CanonicalM004Closure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) : Prop where
  m003Closure : CanonicalM003Closure realization
  birthInstructionExists :
    ∃ response value,
      ∃ hPair : IsResponseSteeringPair realization response value,
        ∃ output : ResponseCoupledBirthInstruction next,
          IsDerivedCanonicalBirthLaw
            realization response value hPair output
  birthInstructionUniqueForPair :
    ∀ (response : ExactFractionMatrix
        (boundary next).length (boundary next).length)
      (value : ExactFraction)
      (hPair : IsResponseSteeringPair realization response value),
        ∃! output : ResponseCoupledBirthInstruction next,
          IsDerivedCanonicalBirthLaw
            realization response value hPair output
  representativeIndependent :
    ∀ (leftResponse rightResponse : ExactFractionMatrix
        (boundary next).length (boundary next).length)
      (leftValue rightValue : ExactFraction)
      (hLeftPair : IsResponseSteeringPair
        realization leftResponse leftValue)
      (hRightPair : IsResponseSteeringPair
        realization rightResponse rightValue)
      (leftOutput rightOutput : ResponseCoupledBirthInstruction next),
        IsDerivedCanonicalBirthLaw
          realization leftResponse leftValue hLeftPair leftOutput →
        IsDerivedCanonicalBirthLaw
          realization rightResponse rightValue hRightPair rightOutput →
        BirthInstructionSameValue leftOutput rightOutput

/-- Every canonical state-directed realization satisfies the complete M004
interface.  Its existence, positivity, and response-domain inputs are consumed
from `CanonicalM003Closure`; no parent coordinate is selected again. -/
theorem canonicalM004Closure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    CanonicalM004Closure realization := by
  let m003 : CanonicalM003Closure realization :=
    canonicalM003Closure realization
  refine {
    m003Closure := m003
    birthInstructionExists := ?_
    birthInstructionUniqueForPair := ?_
    representativeIndependent := ?_ }
  · obtain ⟨response, value, hPair⟩ := m003.responseSteeringExists
    have hPositive : PositiveSteering value :=
      m003.everySteeringPositive response value hPair
    obtain ⟨output, hOutput⟩ :=
      birthLaw_exists realization response value hPair hPositive
    exact ⟨response, value, hPair, output, hPositive, hOutput⟩
  · intro response value hPair
    have hPositive : PositiveSteering value :=
      m003.everySteeringPositive response value hPair
    obtain ⟨output, hOutput⟩ :=
      birthLaw_exists realization response value hPair hPositive
    refine ⟨output, ⟨hPositive, hOutput⟩, ?_⟩
    intro candidate hCandidate
    exact derivedCanonicalBirthLaw_unique
      realization response value hPair hCandidate ⟨hPositive, hOutput⟩
  · intro leftResponse rightResponse leftValue rightValue
      hLeftPair hRightPair leftOutput rightOutput hLeft hRight
    obtain ⟨hLeftPositive, hLeftCanonical⟩ := hLeft
    obtain ⟨hRightPositive, hRightCanonical⟩ := hRight
    unfold IsCanonicalBirthLaw at hLeftCanonical hRightCanonical
    rw [hLeftCanonical, hRightCanonical]
    exact responseSteeringPairs_give_same_birthLaw
      realization m003.positiveSteeringDomain.1
      leftResponse rightResponse hLeftPair hRightPair
      hLeftPositive hRightPositive

/-- Immutable M004 output boundary for C008.  It hides the particular exact
response representative and all proof witnesses while retaining the Core
instruction as the only output object. -/
def IsCanonicalBirthInstructionHandoff
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (output : ResponseCoupledBirthInstruction next) : Prop :=
  ∃ response value,
    ∃ hPair : IsResponseSteeringPair realization response value,
      IsDerivedCanonicalBirthLaw
        realization response value hPair output

/-- The closed M004 interface always supplies an immutable instruction handoff. -/
theorem canonicalBirthInstructionHandoff_exists
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    ∃ output : ResponseCoupledBirthInstruction next,
      IsCanonicalBirthInstructionHandoff realization output := by
  obtain ⟨response, value, hPair, output, hOutput⟩ :=
    (canonicalM004Closure realization).birthInstructionExists
  exact ⟨output, response, value, hPair, hOutput⟩

/-- Any two canonical handoffs have identical provenance support and exact
scalar values, even when their C006 response representatives differ. -/
theorem canonicalBirthInstructionHandoff_sameValue
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    {left right : ResponseCoupledBirthInstruction next}
    (hLeft : IsCanonicalBirthInstructionHandoff realization left)
    (hRight : IsCanonicalBirthInstructionHandoff realization right) :
    BirthInstructionSameValue left right := by
  obtain ⟨leftResponse, leftValue, hLeftPair, hLeftOutput⟩ := hLeft
  obtain ⟨rightResponse, rightValue, hRightPair, hRightOutput⟩ := hRight
  exact (canonicalM004Closure realization).representativeIndependent
    leftResponse rightResponse leftValue rightValue
    hLeftPair hRightPair left right hLeftOutput hRightOutput

/-- Public M004 closure contract, including the immutable downstream handoff. -/
def CanonicalM004ClosureContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next),
      CanonicalM004Closure realization ∧
      (∃ output : ResponseCoupledBirthInstruction next,
        IsCanonicalBirthInstructionHandoff realization output) ∧
      (∀ (left right : ResponseCoupledBirthInstruction next),
        IsCanonicalBirthInstructionHandoff realization left →
        IsCanonicalBirthInstructionHandoff realization right →
        BirthInstructionSameValue left right)

/-- The canonical M004 closure and downstream-handoff contract is inhabited. -/
theorem canonicalM004ClosureContract : CanonicalM004ClosureContract := by
  intro X next realization
  refine ⟨canonicalM004Closure realization, ?_, ?_⟩
  · exact canonicalBirthInstructionHandoff_exists realization
  · intro left right hLeft hRight
    exact canonicalBirthInstructionHandoff_sameValue
      realization hLeft hRight

end CNNAProofs.M003M004
