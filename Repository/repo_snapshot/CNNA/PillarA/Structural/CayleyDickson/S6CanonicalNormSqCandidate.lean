import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate
import CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

/--
Canonical Slot-2 diagonal lift target on the already fixed common carrier.
The norm itself is left explicit; only its required values on the diagonal Schur/
center embeddings are recorded here.
-/
def CanonicalDiagonalNormSqLift
    (X : CayleyDicksonSource Cell T)
    (normSq : CanonicalBlockTuple X → ℝ) : Prop :=
  normSq (CanonicalBlockTuple.embedOuter X .left .left X.schur.brightBrightSchur) =
      MatrixNorm.Analytic.frobSq X.schur.brightBrightSchur ∧
    normSq (CanonicalBlockTuple.embedCenter X (triadicCenterMatrix X)) =
      MatrixNorm.Analytic.frobSq (triadicCenterMatrix X) ∧
    normSq (CanonicalBlockTuple.embedOuter X .right .right X.schur.darkDarkSchur) =
      MatrixNorm.Analytic.frobSq X.schur.darkDarkSchur

/--
Canonical Slot-2 data on the fixed Slot-1 carrier and product.
At this stage we do not pretend to have a closed formula for the norm on all five
components; instead we record exactly the remaining proof-carrying obligations.
-/
structure CanonicalNormSqCandidate
    (X : CayleyDicksonSource Cell T) where
  normSq : CanonicalBlockTuple X → ℝ
  liftDiagonalToCanonicalNormSq :
    CanonicalDiagonalNormSqLift X normSq
  normSqMultiplicativeOnCanonicalProduct :
    ∀ a b : CanonicalBlockTuple X,
      normSq (CanonicalBlockTuple.mul X a b) =
        normSq a * normSq b

/-- Canonical Slot-2 surface on the fixed common carrier and canonical product. -/
def canonicalNormSqProductSurfaceOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqCandidate X) :
    CanonicalNormSqProductSurface X where
  Carrier := CanonicalBlockTuple X
  mul := CanonicalBlockTuple.mul X
  normSq := h.normSq

/-- Package the proof-carrying canonical Slot-2 data as the existing boundary object. -/
def canonicalNormSqBoundaryOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqCandidate X) :
    SchurBlockNormSqMultiplicativityBoundary X where
  scaffold := normSqMultiplicativityScaffoldSeedOf X
  surface := canonicalNormSqProductSurfaceOf X h
  embedOuter := CanonicalBlockTuple.embedOuter X
  embedCenter := CanonicalBlockTuple.embedCenter X
  liftDiagonalToCanonicalNormSq :=
    CanonicalDiagonalNormSqLift X h.normSq
  normSqMultiplicativeOnCanonicalProduct := by
    intro a b
    exact h.normSqMultiplicativeOnCanonicalProduct a b

theorem canonicalNormSqBoundary_liftDiagonalToCanonicalNormSq
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqCandidate X) :
    (canonicalNormSqBoundaryOf X h).liftDiagonalToCanonicalNormSq := by
  exact h.liftDiagonalToCanonicalNormSq

/--
Canonical Slot-2 frontier: on the already fixed common carrier and product, what remains
is the existence of a norm together with the diagonal lift and multiplicativity proof.
-/
def CanonicalNormSqMultiplicativityFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (CanonicalNormSqCandidate X)

theorem canonicalNormSqMultiplicativityFrontier_implies_slot2Boundary
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqMultiplicativityFrontier (Cell := Cell) (T := T) X) :
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqBoundaryOf X witness⟩

theorem canonicalNormSqMultiplicativityFrontier_implies_slot2Frontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqMultiplicativityFrontier (Cell := Cell) (T := T) X) :
    SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X := by
  exact slot2Boundary_implies_frontier X
    (canonicalNormSqMultiplicativityFrontier_implies_slot2Boundary X h)

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
