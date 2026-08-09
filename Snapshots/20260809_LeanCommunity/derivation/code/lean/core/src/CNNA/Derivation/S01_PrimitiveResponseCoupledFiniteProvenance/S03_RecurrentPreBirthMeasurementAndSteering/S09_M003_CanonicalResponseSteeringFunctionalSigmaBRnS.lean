import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S06_M005_ConductanceUnitNormalizationIndependence
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S06_C007_InterBirthDirectedResponseRnSnplus1
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S08_C015_ActiveLinearSteeringModePhiXX

/-!
Paper 1.3.9 / M003 — canonical response-steering functional
`Sigma_b[R_n,s]`.

For the C004 next slot `s`, M001 contains the slot parent in the C007 response
boundary.  M003 takes the exact parent-port diagonal aggregate, regards it in
the fixed N001/M005 conductance unit `C_star = 1`, and passes it through C015's fixed active-path identity convention `phi(x)=x`.

The diagonal aggregate is written as a finite sum over all response-boundary
coordinates whose address is the slot parent.  On the duplicate-free C005/M001
carrier this is exactly the unique parent diagonal entry.  This extensional
form avoids adding a separately chosen positional index and makes replacement
of unnormalised C006 fraction representatives harmless.

M003 introduces no numerical rank term, forward/backward bias, fitted sign,
coefficient, clipping, logarithm, saturation, birth event, conductance update,
or successor state.  Those downstream operations, if admitted, belong to
M004 or to separately named control nodes.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
open NextOpenProvenanceSlot
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open InterBirthDirectedResponse
open ActiveLinearSteeringModePhiXX

namespace CanonicalResponseSteeringFunctionalSigmaBRnS

/-- The terminal word occurs in its own root-to-terminal prefix chain. -/
theorem terminal_mem_prefixChainAux {b : BranchingParameter}
    (pref rest : ProvenanceAddress b) :
    pref ++ rest ∈ prefixChainAux pref rest := by
  induction rest generalizing pref with
  | nil =>
      rw [List.append_nil]
      exact List.Mem.head []
  | cons localRank tail ih =>
      change
        pref ++ (localRank :: tail) ∈
          pref :: prefixChainAux (pref ++ [localRank]) tail
      apply List.Mem.tail
      have hTail :
          (pref ++ [localRank]) ++ tail ∈
            prefixChainAux (pref ++ [localRank]) tail :=
        ih (pref ++ [localRank])
      have hWord :
          (pref ++ [localRank]) ++ tail = pref ++ (localRank :: tail) := by
        exact List.append_assoc pref [localRank] tail
      rw [hWord] at hTail
      exact hTail

/-- The C004 slot parent is one of M001's causal predecessor ports. -/
theorem parent_mem_causalPredecessorPorts {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    parentAddress next ∈ causalPredecessorPorts next := by
  unfold causalPredecessorPorts
  have h :
      ([] : ProvenanceAddress X.grammar.branching) ++ parentAddress next ∈
        prefixChainAux [] (parentAddress next) :=
    terminal_mem_prefixChainAux [] (parentAddress next)
  exact h

/-- Consequently the slot parent is present in the exact C007 response boundary. -/
theorem parent_mem_boundary {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    parentAddress next ∈ boundary next := by
  apply birthLocalPort_mem_boundary next
  exact Or.inl (parent_mem_causalPredecessorPorts next)

/-- One diagonal contribution is retained exactly when its C007 boundary
address is the C004 slot parent. -/
def parentDiagonalTerm {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (index : Fin (boundary next).length) : ExactFraction :=
  if boundaryAddress next index = parentAddress next then
    lambda index index
  else
    ExactFraction.zero

/-- Exact parent-port self-response.  The sum form is extensional in the M001
address-labelled boundary and does not introduce an independent matrix index. -/
def parentSelfResponse {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) :
    ExactFraction :=
  Fin.foldl (boundary next).length
    (fun acc index => ExactFraction.add acc (parentDiagonalTerm next lambda index))
    ExactFraction.zero

/-- M005 fixes only the conductance-unit representative.  Because N001 selects
`C_star = 1`, the unit-normalised exact parent response is represented by the
same C006 fraction value; no division primitive or new parameter is introduced. -/
def unitNormalizedParentResponse {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) :
    ExactFraction :=
  parentSelfResponse next lambda

/-- The M005/N001 token used by M003 is exactly the rational unit one. -/
theorem selected_conductance_unit_eq_one :
    n001ConductanceUnit InitialConductanceNormalization.canonical = 1 := by
  exact n001ConductanceUnit_eq_one InitialConductanceNormalization.canonical

/-- Canonical M003 functional.  C015 fixes the identity convention on the
exact C006 scalar domain; it does not select among formal modes. -/
def sigma {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) :
    ExactFraction :=
  phi (unitNormalizedParentResponse next lambda)

/-- Pointwise relation characterising the unique M003 output value. -/
def IsCanonicalResponseSteering {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction) : Prop :=
  ExactFraction.SameValue value (sigma next lambda)

/-- C015 introduces no further change after unit normalisation. -/
theorem sigma_eq_unitNormalizedParentResponse {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) :
    sigma next lambda = unitNormalizedParentResponse next lambda :=
  rfl

/-- With the fixed unit representative `C_star=1`, M003 is exactly the
parent-port self-response value. -/
theorem sigma_eq_parentSelfResponse {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) :
    sigma next lambda = parentSelfResponse next lambda :=
  rfl

/-- Strict positivity of an exact steering representative.  Because every C006
denominator is positive, this is the numerator sign condition needed by the
positive C005 conductance carrier. -/
def PositiveSteering (value : ExactFraction) : Prop :=
  0 < value.num

/-- Each selected or rejected parent-diagonal term respects C006 matrix-value
equality. -/
theorem parentDiagonalTerm_respects_matrixSameValue
    {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {left right : ExactFractionMatrix (boundary next).length (boundary next).length}
    (hMatrix : MatrixSameValue left right)
    (index : Fin (boundary next).length) :
    ExactFraction.SameValue
      (parentDiagonalTerm next left index)
      (parentDiagonalTerm next right index) := by
  unfold parentDiagonalTerm
  by_cases hParent : boundaryAddress next index = parentAddress next
  · rw [if_pos hParent, if_pos hParent]
    exact hMatrix index index
  · rw [if_neg hParent, if_neg hParent]
    exact ExactFraction.sameValue_refl ExactFraction.zero

/-- The exact parent-port aggregate is independent of the raw numerator and
denominator representatives chosen for the C007 response matrix. -/
theorem parentSelfResponse_respects_matrixSameValue
    {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {left right : ExactFractionMatrix (boundary next).length (boundary next).length}
    (hMatrix : MatrixSameValue left right) :
    ExactFraction.SameValue
      (parentSelfResponse next left)
      (parentSelfResponse next right) := by
  unfold parentSelfResponse
  apply ExactFraction.foldl_add_respects_sameValue
  · intro index
    exact parentDiagonalTerm_respects_matrixSameValue next hMatrix index
  · exact ExactFraction.sameValue_refl ExactFraction.zero

/-- Therefore the complete M003 functional is extensional in the exact C007
response value and does not depend on its raw fraction encoding. -/
theorem sigma_respects_matrixSameValue
    {X : ResponseCapableState}
    (next : NextOpenSlot X)
    {left right : ExactFractionMatrix (boundary next).length (boundary next).length}
    (hMatrix : MatrixSameValue left right) :
    ExactFraction.SameValue (sigma next left) (sigma next right) := by
  change
    ExactFraction.SameValue
      (parentSelfResponse next left)
      (parentSelfResponse next right)
  exact parentSelfResponse_respects_matrixSameValue next hMatrix

/-- The canonical functional always supplies an M003 value. -/
theorem steering_exists {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) :
    ∃ value : ExactFraction, IsCanonicalResponseSteering next lambda value := by
  refine ⟨sigma next lambda, ?_⟩
  exact ExactFraction.sameValue_refl (sigma next lambda)

/-- For one exact C007 response value, the M003 output is unique modulo the
same exact-fraction value relation used by C006 and C007. -/
theorem steering_unique {X : ResponseCapableState}
    (next : NextOpenSlot X)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    {left right : ExactFraction}
    (hLeft : IsCanonicalResponseSteering next lambda left)
    (hRight : IsCanonicalResponseSteering next lambda right) :
    ExactFraction.SameValue left right := by
  exact ExactFraction.sameValue_trans hLeft
    (ExactFraction.sameValue_symm hRight)

/-- Any two C007 response representatives for the same state-directed
realisation induce the same M003 steering value. -/
theorem response_representatives_give_same_steering
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (hDomain : InResponseDomain realization)
    (left right : ExactFractionMatrix (boundary next).length (boundary next).length)
    (hLeft : IsInterBirthDirectedResponse realization left)
    (hRight : IsInterBirthDirectedResponse realization right) :
    ExactFraction.SameValue (sigma next left) (sigma next right) := by
  apply sigma_respects_matrixSameValue next
  exact response_unique realization hDomain left right hLeft hRight

/-- Combined C007-to-M003 relation used by the later M004 handoff. -/
def IsResponseSteeringPair {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction) : Prop :=
  IsInterBirthDirectedResponse realization lambda ∧
    IsCanonicalResponseSteering next lambda value

/-- One C007/M003 pair whose exact scalar is admissible for positive C005
conductance creation. -/
def IsPositiveResponseSteeringPair {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length)
    (value : ExactFraction) : Prop :=
  IsResponseSteeringPair realization lambda value ∧ PositiveSteering value

/-- Canonical directed-Kron parent positivity at one realized state.  Core keeps
this property as an explicit interface because the proof uses the mathlib-based
Schur/DtN layer.  The proof package proves it for every canonical
realization without an externally supplied parent coordinate. -/
def DirectedKronParentPositivityAt {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) : Prop :=
  ∀ lambda value,
    IsResponseSteeringPair realization lambda value → PositiveSteering value

/-- Exact active steering domain: C007 exists uniquely and every exact
response-steering representative has strictly positive parent-port steering.
The mathlib-free Core states this domain; the proof package proves universal
canonical inhabitance and exposes it through the closed M003 interface. -/
def InPositiveSteeringDomain {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) : Prop :=
  InResponseDomain realization ∧ DirectedKronParentPositivityAt realization

/-- The active-domain statement is definitionally the conjunction above. -/
theorem inPositiveSteeringDomain_iff {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    InPositiveSteeringDomain realization ↔
      InResponseDomain realization ∧ DirectedKronParentPositivityAt realization :=
  Iff.rfl

/-- Every realised C007 response-domain point has an M003 steering pair. -/
theorem responseSteeringPair_exists
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (hDomain : InResponseDomain realization) :
    ∃ lambda value,
      IsResponseSteeringPair realization lambda value := by
  obtain ⟨lambda, hResponse⟩ := response_exists realization hDomain
  refine ⟨lambda, sigma next lambda, hResponse, ?_⟩
  exact ExactFraction.sameValue_refl (sigma next lambda)

/-- The complete C007-to-M003 handoff determines one exact steering value even
when both the response matrix and scalar use unnormalised fraction encodings. -/
theorem responseSteeringPair_value_unique
    {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (hDomain : InResponseDomain realization)
    (leftResponse rightResponse :
      ExactFractionMatrix (boundary next).length (boundary next).length)
    {leftValue rightValue : ExactFraction}
    (hLeft : IsResponseSteeringPair realization leftResponse leftValue)
    (hRight : IsResponseSteeringPair realization rightResponse rightValue) :
    ExactFraction.SameValue leftValue rightValue := by
  have hResponseValue : MatrixSameValue leftResponse rightResponse :=
    response_unique realization hDomain leftResponse rightResponse hLeft.1 hRight.1
  have hFunctionalValue :
      ExactFraction.SameValue
        (sigma next leftResponse)
        (sigma next rightResponse) :=
    sigma_respects_matrixSameValue next hResponseValue
  exact ExactFraction.sameValue_trans hLeft.2
    (ExactFraction.sameValue_trans hFunctionalValue
      (ExactFraction.sameValue_symm hRight.2))

end CanonicalResponseSteeringFunctionalSigmaBRnS

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
