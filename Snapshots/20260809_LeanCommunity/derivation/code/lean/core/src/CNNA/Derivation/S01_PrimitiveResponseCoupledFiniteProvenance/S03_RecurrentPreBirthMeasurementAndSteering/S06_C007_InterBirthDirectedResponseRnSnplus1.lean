import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S05_M002_BirthCutInteriorDomainTheorem

/-!
Paper 1.3.6 / C007 — inter-birth directed response `Rₙ(sₙ₊₁)`.

C007 is the first node that wires the current C005 conductance state into the
birth-local response chain.  The C004 next slot fixes the M001 ordered cut; C007
then realizes the current network as the source/out-degree directed matrix

  K[u,u] = sum_v c(u,v),      K[u,v] = -c(u,v) for u != v,

using every directed C005 conductance and no symmetrization or transpose.  The
M001 boundary coordinates precede the interior coordinates.  Since M001
partitions the complete already-born carrier, no external port or grounded load
is introduced, and the unborn C004 child is absent from all matrix coordinates.

Lean does not choose normalized `Rat` block entries from the exact conductance
sums.  Instead a `StateDirectedBlockRealization` supplies canonical rational
C006 blocks together with entrywise `MatrixRepresents` proofs against the
constructive exact-fraction sums below.  This is the theorematic counterpart of
Python's deterministic `Fraction` matrix assembly.  M002 domain membership then
supplies existence and uniqueness of the C006 response.

C007 defines only the measured response after birth n and before birth n+1.  It
does not choose a steering functional, transform the response, or execute the
next birth.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
open NextOpenProvenanceSlot
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open BirthCutInteriorDomainTheorem

namespace InterBirthDirectedResponse

/-- Exact sum of all outgoing C005 conductances from one born source address. -/
def outgoingSum {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source : ProvenanceAddress b) : ExactFraction :=
  edges.foldl
    (fun acc edge =>
      if edge.source = source then
        ExactFraction.add acc (ExactFraction.ofRat edge.value)
      else acc)
    ExactFraction.zero

/-- Exact sum on one ordered C005 source-target pair.  C005 already guarantees
at most one stored entry per ordered pair; using a fold keeps the definition
constructive and extensional. -/
def orderedPairSum {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) : ExactFraction :=
  edges.foldl
    (fun acc edge =>
      if edge.source = source then
        if edge.target = target then
          ExactFraction.add acc (ExactFraction.ofRat edge.value)
        else acc
      else acc)
    ExactFraction.zero

/-- Fixed C007 source/out-degree matrix entry. -/
def directedMatrixEntry {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b) : ExactFraction :=
  if source = target then
    outgoingSum edges source
  else
    ExactFraction.sub ExactFraction.zero (orderedPairSum edges source target)

/-- The diagonal is exactly total outgoing directed conductance. -/
theorem directedMatrixEntry_self {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source : ProvenanceAddress b) :
    directedMatrixEntry edges source source = outgoingSum edges source := by
  unfold directedMatrixEntry
  rw [if_pos rfl]

/-- Off-diagonal entries carry the negative source-to-target conductance. -/
theorem directedMatrixEntry_of_ne {b : BranchingParameter}
    (edges : List (DirectedConductance b))
    (source target : ProvenanceAddress b)
    (hDistinct : source ≠ target) :
    directedMatrixEntry edges source target =
      ExactFraction.sub ExactFraction.zero
        (orderedPairSum edges source target) := by
  unfold directedMatrixEntry
  rw [if_neg hDistinct]

/-- Address of one M001 boundary coordinate. -/
def boundaryAddress {X : ResponseCapableState} (next : NextOpenSlot X)
    (i : Fin (boundary next).length) : ProvenanceAddress X.grammar.branching :=
  (boundary next).get i

/-- Address of one M001 interior coordinate. -/
def interiorAddress {X : ResponseCapableState} (next : NextOpenSlot X)
    (i : Fin (interior next).length) : ProvenanceAddress X.grammar.branching :=
  (interior next).get i

/-- Raw exact C005 matrix restricted to boundary rows and boundary columns. -/
def rawKBB {X : ResponseCapableState} (next : NextOpenSlot X) :
    ExactFractionMatrix (boundary next).length (boundary next).length :=
  fun i j =>
    directedMatrixEntry X.conductances
      (boundaryAddress next i) (boundaryAddress next j)

/-- Raw exact C005 matrix restricted to boundary rows and interior columns. -/
def rawKBI {X : ResponseCapableState} (next : NextOpenSlot X) :
    ExactFractionMatrix (boundary next).length (interior next).length :=
  fun i j =>
    directedMatrixEntry X.conductances
      (boundaryAddress next i) (interiorAddress next j)

/-- Raw exact C005 matrix restricted to interior rows and boundary columns. -/
def rawKIB {X : ResponseCapableState} (next : NextOpenSlot X) :
    ExactFractionMatrix (interior next).length (boundary next).length :=
  fun i j =>
    directedMatrixEntry X.conductances
      (interiorAddress next i) (boundaryAddress next j)

/-- Raw exact C005 matrix restricted to interior rows and interior columns. -/
def rawKII {X : ResponseCapableState} (next : NextOpenSlot X) :
    ExactFractionMatrix (interior next).length (interior next).length :=
  fun i j =>
    directedMatrixEntry X.conductances
      (interiorAddress next i) (interiorAddress next j)

/-- Canonical rational C006 blocks represent exactly the C005 source/out-degree
entries in the M001 order. -/
def RealizesStateDirectedBlocks {X : ResponseCapableState}
    (next : NextOpenSlot X) (blocks : BirthCutBlocks next) : Prop :=
  MatrixRepresents (rawKBB next) blocks.kBB ∧
  MatrixRepresents (rawKBI next) blocks.kBI ∧
  MatrixRepresents (rawKIB next) blocks.kIB ∧
  MatrixRepresents (rawKII next) blocks.kII

/-- One canonical-rational realization of the exact state-directed matrix.
Python constructs these normalized values; Lean records their exact-value
identity without choosing a normalizer. -/
structure StateDirectedBlockRealization (X : ResponseCapableState)
    (next : NextOpenSlot X) where
  blocks : BirthCutBlocks next
  realizes : RealizesStateDirectedBlocks next blocks

/-- C007's response relation for one exact state-directed block realization. -/
def IsInterBirthDirectedResponse {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (lambda : ExactFractionMatrix (boundary next).length (boundary next).length) : Prop :=
  IsSchurDtnResponse realization.blocks lambda

/-- C007 domain membership is exactly the M002 domain for the realized blocks. -/
def InResponseDomain {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) : Prop :=
  InExactDomain next realization.blocks

/-- The C007 domain is definitionally the exact M002 domain, with no added
threshold or sufficient-condition surrogate. -/
theorem inResponseDomain_iff_m002 {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next) :
    InResponseDomain realization ↔ InExactDomain next realization.blocks :=
  Iff.rfl

/-- Every state-directed realization in the exact M002 domain has a C007
inter-birth response. -/
theorem response_exists {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (hDomain : InResponseDomain realization) :
    ∃ lambda : ExactFractionMatrix (boundary next).length (boundary next).length,
      IsInterBirthDirectedResponse realization lambda := by
  change ∃ lambda : ExactFractionMatrix (boundary next).length (boundary next).length,
    IsSchurDtnResponse realization.blocks lambda
  exact exactDomain_response_exists next realization.blocks hDomain

/-- The measured C007 rational response value is unique for one exact
state-directed realization on the M002 domain, independently of normalization. -/
theorem response_unique {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (hDomain : InResponseDomain realization)
    (left right : ExactFractionMatrix (boundary next).length (boundary next).length)
    (hLeft : IsInterBirthDirectedResponse realization left)
    (hRight : IsInterBirthDirectedResponse realization right) :
    MatrixSameValue left right := by
  exact exactDomain_response_unique next realization.blocks hDomain
    left right hLeft hRight

/-- Any raw response matrix with the same exact rational values is the same C007
response.  This is the explicit output-side normalization bridge to Python's
canonical `Fraction` matrix. -/
theorem response_of_sameValue {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    {left right : ExactFractionMatrix (boundary next).length (boundary next).length}
    (hResponse : IsInterBirthDirectedResponse realization right)
    (hValue : MatrixSameValue left right) :
    IsInterBirthDirectedResponse realization left := by
  exact BirthLocalSchurDtnPrimitive.response_of_sameValue
    realization.blocks hResponse hValue

/-- The next C004 child is not a response boundary coordinate: measurement is
strictly pre-birth. -/
theorem unborn_child_not_in_boundary {X : ResponseCapableState}
    (next : NextOpenSlot X) : next.val ∉ boundary next :=
  child_not_in_boundary next

/-- The next C004 child is also absent from the eliminated interior. -/
theorem unborn_child_not_in_interior {X : ResponseCapableState}
    (next : NextOpenSlot X) : next.val ∉ interior next :=
  child_not_in_interior next

end InterBirthDirectedResponse

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
