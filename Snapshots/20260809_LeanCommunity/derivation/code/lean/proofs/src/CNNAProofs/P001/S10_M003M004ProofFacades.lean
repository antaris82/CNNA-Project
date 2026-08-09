import CNNAProofs.P001.S09_CanonicalBackboneReachability
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S10_M004_ResponseCoupledBirthLawBirthlawB

/-!
# P001 R7 — thin M003/M004 proof facades

This module exposes the already kernel-verified R6 canonical birth-cut closure at
M003 and M004 without duplicating any Schur/DtN/Kron, maximum-principle,
matrix-structure, or reachability proof.

The M003 facade derives `InPositiveSteeringDomain` and pointwise
`PositiveSteering` directly from `canonicalBirthCutClosure_derived`.  The M004
facade reuses the Core constructors and theorems `birthLaw_exists`,
`birthLaw_unique`, and `responseSteeringPairs_give_same_birthLaw`.  Its local
predicate merely hides the proof argument witnessing positivity; it adds no
model field and no alternative birth-law definition.
-/

namespace CNNAProofs.P001

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open NextOpenProvenanceSlot
open InterBirthDirectedResponse
open CanonicalResponseSteeringFunctionalSigmaBRnS
open ResponseCoupledBirthLawBirthlawB

/-- R7 M003 facade: the actual canonical C005/M001/C007 realization lies in the
strictly positive steering domain derived by P001. -/
theorem canonicalInPositiveSteeringDomain
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next) :
    InPositiveSteeringDomain realization := by
  have closure : CanonicalBirthCutClosure realization distinguished :=
    canonicalBirthCutClosure_derived realization distinguished
  exact ⟨closure.c007ResponseDomain, closure.m003ParentPositivity⟩

/-- R7 pointwise M003 facade: every exact C007/M003 representative pair on the
canonical realization has strictly positive steering. -/
theorem canonicalResponseSteeringPair_positive
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next)
    (response : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization response value) :
    PositiveSteering value := by
  exact
    (canonicalBirthCutClosure_derived realization distinguished).m003ParentPositivity
      response value hPair

/-- M004 facade predicate with the P001-derived positivity proof hidden behind
an existential.  The output remains Core's `birthLaw`; no second constructor is
introduced. -/
def IsDerivedCanonicalBirthLaw
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (response : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization response value)
    (output : ResponseCoupledBirthInstruction next) : Prop :=
  ∃ hPositive : PositiveSteering value,
    IsCanonicalBirthLaw realization response value hPair hPositive output

/-- R7 M004 existence facade for one valid canonical response/steering pair. -/
theorem derivedCanonicalBirthLaw_exists
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next)
    (response : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization response value) :
    ∃ output : ResponseCoupledBirthInstruction next,
      IsDerivedCanonicalBirthLaw realization response value hPair output := by
  have hPositive : PositiveSteering value :=
    canonicalResponseSteeringPair_positive
      realization distinguished response value hPair
  obtain ⟨output, hOutput⟩ :=
    birthLaw_exists realization response value hPair hPositive
  exact ⟨output, hPositive, hOutput⟩

/-- R7 M004 uniqueness facade.  Positivity proofs are propositionally unique,
so hiding the proof argument does not weaken exact output uniqueness. -/
theorem derivedCanonicalBirthLaw_unique
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (response : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization response value)
    {left right : ResponseCoupledBirthInstruction next}
    (hLeft : IsDerivedCanonicalBirthLaw realization response value hPair left)
    (hRight : IsDerivedCanonicalBirthLaw realization response value hPair right) :
    left = right := by
  obtain ⟨hLeftPositive, hLeftCanonical⟩ := hLeft
  obtain ⟨hRightPositive, hRightCanonical⟩ := hRight
  have hPositiveProof : hLeftPositive = hRightPositive :=
    Subsingleton.elim hLeftPositive hRightPositive
  cases hPositiveProof
  exact birthLaw_unique
    realization response value hPair hLeftPositive hLeftCanonical hRightCanonical

/-- The P001-derived active M004 law exists uniquely for each valid exact
response/steering pair. -/
theorem derivedCanonicalBirthLaw_existsUnique
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next)
    (response : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction)
    (hPair : IsResponseSteeringPair realization response value) :
    ∃! output : ResponseCoupledBirthInstruction next,
      IsDerivedCanonicalBirthLaw realization response value hPair output := by
  obtain ⟨output, hOutput⟩ :=
    derivedCanonicalBirthLaw_exists
      realization distinguished response value hPair
  refine ⟨output, hOutput, ?_⟩
  intro candidate hCandidate
  exact derivedCanonicalBirthLaw_unique
    realization response value hPair hCandidate hOutput

/-- The canonical positive domain is inhabited by an exact response, steering,
and active M004 birth instruction. -/
theorem canonicalActiveBirthInstruction_exists
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next) :
    ∃ response value,
      ∃ hPair : IsResponseSteeringPair realization response value,
        ∃ output : ResponseCoupledBirthInstruction next,
          IsDerivedCanonicalBirthLaw realization response value hPair output := by
  have hDomain : InResponseDomain realization :=
    (canonicalInPositiveSteeringDomain realization distinguished).1
  obtain ⟨response, value, hPair⟩ :=
    responseSteeringPair_exists realization hDomain
  obtain ⟨output, hOutput⟩ :=
    derivedCanonicalBirthLaw_exists
      realization distinguished response value hPair
  exact ⟨response, value, hPair, output, hOutput⟩

/-- R7 representative-independence facade.  The proof is exactly Core's M004
representative theorem instantiated with P001-derived positivity and response
domain witnesses. -/
theorem derivedCanonicalBirthLaws_sameValue
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (distinguished : DistinguishedParentIndex next)
    (leftResponse rightResponse :
      ExactFractionMatrix (boundary next).length (boundary next).length)
    {leftValue rightValue : ExactFraction}
    (hLeftPair : IsResponseSteeringPair realization leftResponse leftValue)
    (hRightPair : IsResponseSteeringPair realization rightResponse rightValue)
    {leftOutput rightOutput : ResponseCoupledBirthInstruction next}
    (hLeft :
      IsDerivedCanonicalBirthLaw
        realization leftResponse leftValue hLeftPair leftOutput)
    (hRight :
      IsDerivedCanonicalBirthLaw
        realization rightResponse rightValue hRightPair rightOutput) :
    BirthInstructionSameValue leftOutput rightOutput := by
  obtain ⟨hLeftPositive, hLeftCanonical⟩ := hLeft
  obtain ⟨hRightPositive, hRightCanonical⟩ := hRight
  unfold IsCanonicalBirthLaw at hLeftCanonical hRightCanonical
  rw [hLeftCanonical, hRightCanonical]
  exact responseSteeringPairs_give_same_birthLaw
    realization
    (canonicalInPositiveSteeringDomain realization distinguished).1
    leftResponse rightResponse hLeftPair hRightPair
    hLeftPositive hRightPositive

/-- Public R7 facade contract.  It exposes only M003 domain/pointwise positivity,
M004 existence/uniqueness, and the already-proved representative independence. -/
def M003M004ProofFacadeContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (_distinguished : DistinguishedParentIndex next),
      InPositiveSteeringDomain realization ∧
      (∀ (response : ExactFractionMatrix
          (boundary next).length (boundary next).length)
        (value : ExactFraction),
        IsResponseSteeringPair realization response value →
          PositiveSteering value) ∧
      (∀ (response : ExactFractionMatrix
          (boundary next).length (boundary next).length)
        (value : ExactFraction)
        (hPair : IsResponseSteeringPair realization response value),
          ∃! output : ResponseCoupledBirthInstruction next,
            IsDerivedCanonicalBirthLaw
              realization response value hPair output) ∧
      (∀ (leftResponse rightResponse : ExactFractionMatrix
          (boundary next).length (boundary next).length)
        (leftValue rightValue : ExactFraction)
        (hLeftPair : IsResponseSteeringPair realization leftResponse leftValue)
        (hRightPair : IsResponseSteeringPair realization rightResponse rightValue)
        (leftOutput rightOutput : ResponseCoupledBirthInstruction next),
          IsDerivedCanonicalBirthLaw
            realization leftResponse leftValue hLeftPair leftOutput →
          IsDerivedCanonicalBirthLaw
            realization rightResponse rightValue hRightPair rightOutput →
          BirthInstructionSameValue leftOutput rightOutput)

/-- R7 closes the thin M003/M004 proof-facade contract without adding any new
Schur/DtN or birth-law argument. -/
theorem m003M004ProofFacadeContract : M003M004ProofFacadeContract := by
  intro X next realization distinguished
  refine ⟨canonicalInPositiveSteeringDomain realization distinguished, ?_, ?_, ?_⟩
  · intro response value hPair
    exact canonicalResponseSteeringPair_positive
      realization distinguished response value hPair
  · intro response value hPair
    exact derivedCanonicalBirthLaw_existsUnique
      realization distinguished response value hPair
  · intro leftResponse rightResponse leftValue rightValue
      hLeftPair hRightPair leftOutput rightOutput hLeft hRight
    exact derivedCanonicalBirthLaws_sameValue
      realization distinguished leftResponse rightResponse
      hLeftPair hRightPair hLeft hRight

end CNNAProofs.P001
