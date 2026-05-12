import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined
import CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic

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
Canonical Slot-3 candidate on the already fixed Slot-1 carrier and the already
fixed Slot-2 norm. The only additional input is strict positivity of the fixed
canonical norm away from zero.
-/
structure CanonicalDivisionFromNormSqCandidate
    (X : CayleyDicksonSource Cell T) where
  slot2 : CanonicalFixedNormSqCandidate X
  normSq_pos_of_ne_zero :
    ∀ a : CanonicalBlockTuple X,
      a ≠ 0 → 0 < CanonicalBlockTuple.normSq X a

/--
Package the canonical Slot-2 data together with strict positivity away from zero
as the logical Slot-3 boundary.
-/
def canonicalDivisionFromNormSqLogicBoundaryOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqCandidate X) :
    DivisionFromNormSqLogicBoundary X where
  surface := canonicalNormSqProductSurfaceOf X (canonicalNormSqCandidateOf X h.slot2)
  zero := (0 : CanonicalBlockTuple X)
  zero_normSq := by
    change CanonicalBlockTuple.normSq X (0 : CanonicalBlockTuple X) = 0
    exact CanonicalBlockTuple.normSq_zero X
  normSqMultiplicative := by
    intro a b
    exact h.slot2.normSqMultiplicativeOnCanonicalProduct a b
  normSq_pos_of_ne_zero := by
    intro a ha
    exact h.normSq_pos_of_ne_zero a ha

/-- Canonical Slot-3 frontier on the fixed common carrier/product/norm. -/
def CanonicalDivisionFromNormSqFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (CanonicalDivisionFromNormSqCandidate X)

theorem canonicalDivisionFromNormSqCandidate_implies_slot2Boundary
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqCandidate X) :
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X := by
  exact ⟨canonicalFixedNormSqBoundaryOf X h.slot2⟩

theorem canonicalDivisionFromNormSqCandidate_implies_slot3Boundary
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqCandidate X) :
    Slot3DivisionFromNormSqLogic (Cell := Cell) (T := T) X := by
  exact ⟨canonicalDivisionFromNormSqLogicBoundaryOf X h⟩

theorem canonicalDivisionFromNormSqFrontier_implies_slot2Boundary
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact canonicalDivisionFromNormSqCandidate_implies_slot2Boundary X witness

theorem canonicalDivisionFromNormSqFrontier_implies_slot3Boundary
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    Slot3DivisionFromNormSqLogic (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact canonicalDivisionFromNormSqCandidate_implies_slot3Boundary X witness

theorem canonicalDivisionFromNormSqFrontier_implies_slot2Frontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X := by
  exact slot2Boundary_implies_frontier X
    (canonicalDivisionFromNormSqFrontier_implies_slot2Boundary X h)

theorem canonicalDivisionFromNormSqFrontier_implies_slot3Frontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    DivisionFromNormSqLogicFrontier
      slot3DivisionConclusionRemainingResearch X := by
  exact slot3Boundary_implies_frontier X
    (canonicalDivisionFromNormSqFrontier_implies_slot3Boundary X h)

theorem canonicalDivisionFromNormSqFrontier_implies_divisionConclusionFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    DivisionConclusionFrontier
      slot2NormSqMultiplicativityRemainingResearch
      slot3DivisionConclusionRemainingResearch
      X := by
  exact slot2_and_slot3_imply_divisionConclusionFrontier X
    (canonicalDivisionFromNormSqFrontier_implies_slot2Frontier X h)
    (canonicalDivisionFromNormSqFrontier_implies_slot3Frontier X h)

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
