import CNNAProofs.P001.S10_M003M004ProofFacades

/-!
# M003 — canonical response-steering closure

This module closes the public M003 proof interface above the mathlib-free Core.
The canonical parent coordinate is obtained internally from M001 boundary
membership.  Callers provide only the actual state-directed realization.

The result combines response-domain inhabitance, existence of an exact
response-steering pair, and strict positivity of every representative pair.
No Schur/DtN argument is repeated and no numerical parameter is introduced.
-/

namespace CNNAProofs.M003M004

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open NextOpenProvenanceSlot
open InterBirthDirectedResponse
open CanonicalResponseSteeringFunctionalSigmaBRnS
open CNNAProofs.P001

/-- Closed canonical M003 interface.  The distinguished parent coordinate is an
internal proof witness rather than a public argument. -/
structure CanonicalM003Closure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) : Prop where
  positiveSteeringDomain : InPositiveSteeringDomain realization
  responseSteeringExists :
    ∃ response value,
      IsResponseSteeringPair realization response value
  everySteeringPositive :
    ∀ (response : ExactFractionMatrix
        (boundary next).length (boundary next).length)
      (value : ExactFraction),
      IsResponseSteeringPair realization response value →
        PositiveSteering value

/-- Every canonical state-directed realization satisfies the complete M003
interface, with the parent coordinate discharged internally. -/
theorem canonicalM003Closure
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    CanonicalM003Closure realization := by
  obtain ⟨index, hAddress⟩ := distinguishedParentIndex_exists next
  let distinguished : DistinguishedParentIndex next :=
    { index := index
      address_eq_parent := hAddress }
  have hDomain : InPositiveSteeringDomain realization :=
    canonicalInPositiveSteeringDomain realization distinguished
  refine {
    positiveSteeringDomain := hDomain
    responseSteeringExists :=
      responseSteeringPair_exists realization hDomain.1
    everySteeringPositive := ?_ }
  intro response value hPair
  exact canonicalResponseSteeringPair_positive
    realization distinguished response value hPair

/-- Public M003 closure contract without an externally selected boundary index. -/
def CanonicalM003ClosureContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next),
      CanonicalM003Closure realization

/-- The canonical M003 closure contract is inhabited. -/
theorem canonicalM003ClosureContract : CanonicalM003ClosureContract := by
  intro X next realization
  exact canonicalM003Closure realization

end CNNAProofs.M003M004
