import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S03_C006_BirthLocalSchurDtnPrimitive
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S04_M001_CanonicalBirthLocalMeasurementCutCnSnplus1

/-!
Paper 1.3.5 / M002 — birth-cut interior-domain theorem.

M002 closes the domain handoff between the canonical M001 cut and the domain-restricted
C006 Schur/DtN primitive.  M001 determines the ordered boundary/interior carrier
partition but contains no numerical block entries.  Therefore no universal
nonzero-interior invertibility theorem is derivable from the cut alone without
silently importing the later C007 matrix-assembly convention.

The exact M002 domain is instead stated without additional choices: C006 block
data must have the M001 boundary/interior dimensions, and the interior system
must satisfy C006 `IsInteriorAdmissible`, i.e. exact unique solvability of
K_II X = K_IB.  The dimension agreement is enforced in Lean by the type of
`BirthCutBlocks`, not by a separate runtime predicate.

The zero-interior case is unconditional by C006.  For nonempty interiors Python
also supplies an executable same-cut contrast witness (identity K_II versus
zero K_II), demonstrating that M001 dimensions alone cannot determine
admissibility.  Lean does not duplicate that executable witness; it states the
exact domain and proves the handoff to existence/uniqueness of the C006
response.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open NextOpenProvenanceSlot
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive

namespace BirthCutInteriorDomainTheorem

/-- The provenance root is always one of the causal M001 ports. -/
theorem root_is_birthLocalPort {X : ResponseCapableState} (next : NextOpenSlot X) :
    BirthLocalPort next (ResponseCapableState.rootAddress X) := by
  apply Or.inl
  unfold causalPredecessorPorts
  change [] ∈ prefixChainAux [] (parentAddress next)
  cases parentAddress next with
  | nil => exact List.Mem.head []
  | cons localRank tail => exact List.Mem.head _

/-- Hence every canonical M001 boundary is nonempty, supplying C006's boundary
side-condition without a new assumption. -/
theorem canonicalBoundary_nonempty {X : ResponseCapableState} (next : NextOpenSlot X) :
    0 < (boundary next).length := by
  have hRootPort := root_is_birthLocalPort next
  have hRootBoundary := birthLocalPort_mem_boundary next hRootPort
  exact List.length_pos_of_mem hRootBoundary

/-- C006 blocks whose coordinate counts are definitionally those of the
canonical M001 cut.  This is the exact cross-node dimensional handoff. -/
abbrev BirthCutBlocks {X : ResponseCapableState} (next : NextOpenSlot X) :=
  OrderedSchurBlocks (boundary next).length (interior next).length

/-- Package explicitly supplied numerical blocks at the M001 dimensions.
M002 supplies only the already-derived boundary-nonempty proof; it does not
choose any matrix entry. -/
def mkBirthCutBlocks {X : ResponseCapableState} (next : NextOpenSlot X)
    (kBB : RatMatrix (boundary next).length (boundary next).length)
    (kBI : RatMatrix (boundary next).length (interior next).length)
    (kIB : RatMatrix (interior next).length (boundary next).length)
    (kII : RatMatrix (interior next).length (interior next).length) :
    BirthCutBlocks next where
  boundaryNonempty := canonicalBoundary_nonempty next
  kBB := kBB
  kBI := kBI
  kIB := kIB
  kII := kII

/-- Exact M002 domain.  No threshold or extra sufficient condition replaces the
C006 unique-solve predicate. -/
def InExactDomain {X : ResponseCapableState} (next : NextOpenSlot X)
    (blocks : BirthCutBlocks next) : Prop :=
  IsInteriorAdmissible blocks

/-- Language-independent domain identity: M002 acceptance is exactly C006
admissibility after M001 dimensions have been fixed by the type. -/
theorem inExactDomain_iff_c006_admissible {X : ResponseCapableState}
    (next : NextOpenSlot X) (blocks : BirthCutBlocks next) :
    InExactDomain next blocks ↔ IsInteriorAdmissible blocks :=
  Iff.rfl

/-- Every point of the exact M002 domain supplies a C006 response. -/
theorem exactDomain_response_exists {X : ResponseCapableState}
    (next : NextOpenSlot X) (blocks : BirthCutBlocks next)
    (hDomain : InExactDomain next blocks) :
    ∃ lambda : ExactFractionMatrix (boundary next).length (boundary next).length,
      IsSchurDtnResponse blocks lambda := by
  exact response_exists_of_admissible blocks hDomain

/-- The C006 response rational value is unique at every point of the exact
M002 domain, independently of raw-fraction normalization. -/
theorem exactDomain_response_unique {X : ResponseCapableState}
    (next : NextOpenSlot X) (blocks : BirthCutBlocks next)
    (hDomain : InExactDomain next blocks)
    (left right : ExactFractionMatrix (boundary next).length (boundary next).length)
    (hLeft : IsSchurDtnResponse blocks left)
    (hRight : IsSchurDtnResponse blocks right) : MatrixSameValue left right := by
  exact response_unique_of_admissible blocks hDomain left right hLeft hRight

/-- Constructive transport of the C006 zero-interior theorem across an explicit
interior-dimension equality.  Pattern matching on the dimension itself keeps the
dependent block type aligned; the successor case is impossible. -/
private theorem admissible_of_interiorSize_eq_zero {boundary : Nat} :
    (interiorSize : Nat) →
    (blocks : OrderedSchurBlocks boundary interiorSize) →
    interiorSize = 0 →
    IsInteriorAdmissible blocks
  | 0, blocks, _ => zeroInterior_admissible blocks
  | Nat.succ _, _, h => nomatch h

/-- An empty canonical M001 interior is unconditionally inside the C006 domain.
The equality only transports the already typed M001 interior dimension to zero;
no numerical property is assumed. -/
theorem zeroInterior_inExactDomain {X : ResponseCapableState}
    (next : NextOpenSlot X) (blocks : BirthCutBlocks next)
    (hInterior : (interior next).length = 0) :
    InExactDomain next blocks := by
  unfold InExactDomain
  exact admissible_of_interiorSize_eq_zero
    (interior next).length blocks hInterior

end BirthCutInteriorDomainTheorem

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
