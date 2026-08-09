import Mathlib
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S03_C006_BirthLocalSchurDtnPrimitive
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S04_M001_CanonicalBirthLocalMeasurementCutCnSnplus1
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S05_M002_BirthCutInteriorDomainTheorem
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S06_C007_InterBirthDirectedResponseRnSnplus1
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S09_M003_CanonicalResponseSteeringFunctionalSigmaBRnS

/-!
# P001 — Directed Schur/DtN/Kron channel closure contract

This module declares the public proof contract.  The exact semantic bridge is
implemented in `CNNAProofs.P001.S01_ExactSemanticBridge`; this file itself
contains no theorem implementation and introduces no replacement operator, regularized matrix,
selected inverse, pseudoinverse, symmetrization, or grounding vertex.

The contract is split into:

1. an exact bridge from the mathlib rational-matrix semantics to C006;
2. a finite directed maximum principle and triviality of the homogeneous
   interior kernel;
3. existence of the interior solve;
4. uniqueness of the interior solve;
5. response-witness independence;
6. directed Laplacian closure of every exact response representative;
7. strict positivity at one distinguished boundary port.

The hypotheses are stated for a generic finite directed cut.  The canonical
M001/C007 birth cut is a separate instantiation target, so later root, bulk,
and frontier cuts can reuse the same closure and prove only their own cut
hypotheses.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive
open CanonicalBirthLocalMeasurementCut
open NextOpenProvenanceSlot
open BirthCutInteriorDomainTheorem
open InterBirthDirectedResponse
open CanonicalResponseSteeringFunctionalSigmaBRnS

/-- Mathlib matrix carrier used by the proof layer. -/
abbrev RationalMatrix (rows cols : Nat) := Matrix (Fin rows) (Fin cols) ℚ

/-- Explicit carrier bridge from the mathlib-free Core `RatMatrix` alias to
    the proof-layer matrix carrier.  This bridge is entrywise and introduces no
    multiplication instance. -/
def coreRatMatrixValue {rows cols : Nat}
    (matrix : RatMatrix rows cols) : RationalMatrix rows cols :=
  Matrix.of matrix

/-- Explicit rectangular matrix product over `ℚ`.  The row-by-column sum is
    stated directly so P001 does not depend on ambiguous `HMul` resolution
    between the reducible `Matrix` and Pi-function carriers. -/
def rationalMatrixMul {rows inner cols : Nat}
    (left : RationalMatrix rows inner)
    (right : RationalMatrix inner cols) : RationalMatrix rows cols :=
  Matrix.of fun i j => ∑ k, left i k * right k j

/-- Boundary and interior coordinates of one ordered finite cut. -/
abbrev CutVertex (boundary interior : Nat) :=
  Sum (Fin boundary) (Fin interior)

/-- Exact rational value of one C006 positive-denominator representative. -/
def exactFractionValue (value : ExactFraction) : ℚ :=
  _root_.mkRat value.num value.den

/-- Entrywise rational value of one C006 response representative. -/
def exactMatrixValue {rows cols : Nat}
    (matrix : ExactFractionMatrix rows cols) : RationalMatrix rows cols :=
  Matrix.of fun i j => exactFractionValue (matrix i j)

/-- Full ordered block entry without changing any C006 matrix coefficient. -/
def blockEntry {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (row column : CutVertex boundary interior) : ℚ :=
  match row, column with
  | Sum.inl i, Sum.inl j => blocks.kBB i j
  | Sum.inl i, Sum.inr j => blocks.kBI i j
  | Sum.inr i, Sum.inl j => blocks.kIB i j
  | Sum.inr i, Sum.inr j => blocks.kII i j

/-- A positive directed conductance is represented by a strictly negative
    off-diagonal source-to-target Laplacian entry. -/
def PositiveArc {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (source target : CutVertex boundary interior) : Prop :=
  source ≠ target ∧ blockEntry blocks source target < 0

/-- Nonempty finite directed path using only positive original conductances. -/
inductive PositivePath {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) :
    CutVertex boundary interior → CutVertex boundary interior → Prop where
  | edge {source target} :
      PositiveArc blocks source target → PositivePath blocks source target
  | tail {source middle target} :
      PositivePath blocks source middle →
      PositiveArc blocks middle target →
      PositivePath blocks source target

/-- Positive path from an interior vertex to the first boundary hit.
    Every source along the path is interior, so the interior harmonic equation is
    available at every propagation step.  This is the proof-relevant form of
    interior-to-boundary reachability used by the maximum principle. -/
inductive InteriorPathToBoundary {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) :
    Fin interior → Fin boundary → Prop where
  | direct {source target} :
      PositiveArc blocks (Sum.inr source) (Sum.inl target) →
      InteriorPathToBoundary blocks source target
  | step {source middle target} :
      PositiveArc blocks (Sum.inr source) (Sum.inr middle) →
      InteriorPathToBoundary blocks middle target →
      InteriorPathToBoundary blocks source target

/-- Exact hypotheses for the generic directed cut.  They mention only the
    original block entries and their induced positive-arc relation. -/
structure DirectedCutHypotheses {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary) : Prop where
  offDiagonalNonpositive :
    ∀ source target, source ≠ target → blockEntry blocks source target ≤ 0
  rowConservative :
    ∀ source, ∑ target, blockEntry blocks source target = 0
  everyInteriorReachesBoundary :
    ∀ i : Fin interior,
      ∃ b : Fin boundary,
        InteriorPathToBoundary blocks i b
  distinguishedReachesOtherBoundary :
    ∃ other : Fin boundary,
      other ≠ distinguished ∧
        PositivePath blocks (Sum.inl distinguished) (Sum.inl other)

/-- Rational potential on the complete ordered cut. -/
abbrev CutPotential (boundary interior : Nat) :=
  CutVertex boundary interior → ℚ

/-- Full directed Laplacian action at one cut vertex. -/
def laplacianAction {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (potential : CutPotential boundary interior)
    (source : CutVertex boundary interior) : ℚ :=
  ∑ target, blockEntry blocks source target * potential target

/-- Boundary values vanish identically. -/
def VanishesOnBoundary {boundary interior : Nat}
    (potential : CutPotential boundary interior) : Prop :=
  ∀ boundaryIndex, potential (Sum.inl boundaryIndex) = 0

/-- The full potential is harmonic at every interior coordinate. -/
def IsInteriorHarmonic {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (potential : CutPotential boundary interior) : Prop :=
  ∀ interiorIndex,
    laplacianAction blocks potential (Sum.inr interiorIndex) = 0

/-- Homogeneous `K_II` equation for one interior vector. -/
def IsInteriorKernelVector {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (vector : Fin interior → ℚ) : Prop :=
  ∀ row, ∑ column, blocks.kII row column * vector column = 0

/-- Extend an interior vector by exact zero boundary data. -/
def zeroBoundaryExtension {boundary interior : Nat}
    (vector : Fin interior → ℚ) : CutPotential boundary interior :=
  fun vertex =>
    match vertex with
    | Sum.inl _ => 0
    | Sum.inr index => vector index

/-- Internal analytical target: the original unregularized interior block has trivial
    kernel under the directed-cut hypotheses. -/
def InteriorKernelTrivial {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) : Prop :=
  ∀ vector : Fin interior → ℚ,
    IsInteriorKernelVector blocks vector → vector = 0

/-- Mathlib-field interpretation of the C006 interior solve equation
    `K_II X = K_IB`. -/
def IsMathlibInteriorSolve {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary) : Prop :=
  rationalMatrixMul (coreRatMatrixValue blocks.kII) solve =
    coreRatMatrixValue blocks.kIB

/-- Harmonic-extension sign convention `K_II H = -K_IB`, where `H = -X`. -/
def IsHarmonicExtension {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (extension : RationalMatrix interior boundary) : Prop :=
  rationalMatrixMul (coreRatMatrixValue blocks.kII) extension =
    -coreRatMatrixValue blocks.kIB

/-- Mathlib rational response associated with one interior solve. -/
def mathlibResponseFromSolve {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary) : RationalMatrix boundary boundary :=
  coreRatMatrixValue blocks.kBB -
    rationalMatrixMul (coreRatMatrixValue blocks.kBI) solve

/-- Required exact bridge between C006's constructive fraction algebra and
    mathlib's rational field/matrix operations. -/
structure ExactSemanticBridge {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) : Prop where
  interiorSolveAgreement :
    ∀ solve,
      IsInteriorSolve blocks solve ↔ IsMathlibInteriorSolve blocks solve
  harmonicSignAgreement :
    ∀ solve,
      IsMathlibInteriorSolve blocks solve ↔
        IsHarmonicExtension blocks (-solve)
  responseValueAgreement :
    ∀ solve,
      exactMatrixValue (responseFromSolve blocks solve) =
        mathlibResponseFromSolve blocks solve

/-- Existence is a separate public closure claim. -/
def InteriorSolveExists {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) : Prop :=
  ∃ solve : RationalMatrix interior boundary,
    IsMathlibInteriorSolve blocks solve

/-- Uniqueness is a separate public closure claim. -/
def InteriorSolveUnique {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) : Prop :=
  ∀ left right : RationalMatrix interior boundary,
    IsMathlibInteriorSolve blocks left →
    IsMathlibInteriorSolve blocks right →
    left = right

/-- Exact C006 response value is independent of both the solve witness and the
    chosen positive-denominator representative. -/
def ResponseWitnessIndependent {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) : Prop :=
  ∀ left right : ExactFractionMatrix boundary boundary,
    IsSchurDtnResponse blocks left →
    IsSchurDtnResponse blocks right →
    MatrixSameValue left right

/-- Directed off-diagonal sign condition on one exact response representative. -/
def ResponseOffDiagonalNonpositive {boundary : Nat}
    (response : ExactFractionMatrix boundary boundary) : Prop :=
  ∀ i j, i ≠ j → exactFractionValue (response i j) ≤ 0

/-- Exact row-conservation condition on one response representative. -/
def ResponseRowConservative {boundary : Nat}
    (response : ExactFractionMatrix boundary boundary) : Prop :=
  ∀ i, ∑ j, exactFractionValue (response i j) = 0

/-- Nonnegative diagonal condition, separated from strict port positivity. -/
def ResponseDiagonalNonnegative {boundary : Nat}
    (response : ExactFractionMatrix boundary boundary) : Prop :=
  ∀ i, 0 ≤ exactFractionValue (response i i)

/-- The directed Laplacian/Z-matrix closure required by P001.  No Hermitian or
    `Matrix.PosDef` assertion is included. -/
def IsDirectedLaplacianResponse {boundary : Nat}
    (response : ExactFractionMatrix boundary boundary) : Prop :=
  ResponseOffDiagonalNonpositive response ∧
  ResponseRowConservative response ∧
  ResponseDiagonalNonnegative response

/-- Strict self-response at the distinguished boundary coordinate. -/
def DistinguishedPortStrictlyPositive {boundary : Nat}
    (distinguished : Fin boundary)
    (response : ExactFractionMatrix boundary boundary) : Prop :=
  0 < exactFractionValue (response distinguished distinguished)

/-- All public conclusions of the generic reusable closure. -/
structure DirectedSchurDtnClosure {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary) : Prop where
  semanticBridge : ExactSemanticBridge blocks
  interiorSolveExists : InteriorSolveExists blocks
  interiorSolveUnique : InteriorSolveUnique blocks
  c006InteriorAdmissible : IsInteriorAdmissible blocks
  responseExists :
    ∃ response : ExactFractionMatrix boundary boundary,
      IsSchurDtnResponse blocks response
  responseWitnessIndependent : ResponseWitnessIndependent blocks
  directedLaplacianClosure :
    ∀ response,
      IsSchurDtnResponse blocks response →
      IsDirectedLaplacianResponse response
  distinguishedPortPositive :
    ∀ response,
      IsSchurDtnResponse blocks response →
      DistinguishedPortStrictlyPositive distinguished response

/-- Public generic theorem shape.  This module declares the proposition but does
    not inhabit it. -/
def ReusableDirectedClosureContract : Prop :=
  ∀ {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (distinguished : Fin boundary),
    DirectedCutHypotheses blocks distinguished →
      DirectedSchurDtnClosure blocks distinguished

/-- Canonical M001 parent coordinate, stated explicitly rather than recovered
    through an implicit choice inside the later proof. -/
structure DistinguishedParentIndex {X : ResponseCapableState}
    (next : NextOpenSlot X) where
  index : Fin (boundary next).length
  address_eq_parent :
    boundaryAddress next index = parentAddress next

/-- Canonical birth-cut target: instantiate the generic closure on the exact
    C007 realization and discharge M003's named positivity predicate. -/
structure CanonicalBirthCutClosure {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (parent : DistinguishedParentIndex next) : Prop where
  genericClosure :
    DirectedSchurDtnClosure realization.blocks parent.index
  c007ResponseDomain : InResponseDomain realization
  m003ParentPositivity : DirectedKronParentPositivityAt realization

/-- Public canonical-instantiation theorem shape.  The generic closure remains
    reusable; this clause records only the M001/C007/M003 handoff. -/
def CanonicalBirthCutClosureContract : Prop :=
  ∀ {X : ResponseCapableState}
    {next : NextOpenSlot X}
    (realization : StateDirectedBlockRealization X next)
    (parent : DistinguishedParentIndex next),
    DirectedCutHypotheses realization.blocks parent.index →
      CanonicalBirthCutClosure realization parent

/-- Complete P001 public contract.  The semantic bridge and the internal
directed maximum-principle/kernel-triviality layer are proved in dedicated
modules; existence and the remaining response closure stay open. -/
def PublicContract : Prop :=
  ReusableDirectedClosureContract ∧ CanonicalBirthCutClosureContract

end CNNAProofs.P001
