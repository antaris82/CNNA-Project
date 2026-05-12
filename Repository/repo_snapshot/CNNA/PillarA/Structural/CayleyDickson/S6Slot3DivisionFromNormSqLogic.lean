import CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition
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
Logical Slot 3 boundary: a canonical norm-square on a closed product surface,
strict positivity away from zero, and multiplicativity. The no-zero-divisors
conclusion is then a purely logical theorem.
-/
structure DivisionFromNormSqLogicBoundary
    (X : CayleyDicksonSource Cell T) where
  surface : CanonicalNormSqProductSurface (Cell := Cell) (T := T) X
  zero : surface.Carrier
  zero_normSq : surface.normSq zero = 0
  normSqMultiplicative :
    ∀ a b : surface.Carrier,
      surface.normSq (surface.mul a b) =
        surface.normSq a * surface.normSq b
  normSq_pos_of_ne_zero :
    ∀ a : surface.Carrier,
      a ≠ zero → 0 < surface.normSq a

/-- Pure logical no-zero-divisors step from positivity and multiplicativity. -/
theorem DivisionFromNormSqLogicBoundary.mul_ne_zero_of_ne_zero
    {X : CayleyDicksonSource Cell T}
    (boundary : DivisionFromNormSqLogicBoundary (Cell := Cell) (T := T) X)
    {a b : boundary.surface.Carrier}
    (ha : a ≠ boundary.zero)
    (hb : b ≠ boundary.zero) :
    boundary.surface.mul a b ≠ boundary.zero := by
  intro hmul
  have haPos : 0 < boundary.surface.normSq a :=
    boundary.normSq_pos_of_ne_zero a ha
  have hbPos : 0 < boundary.surface.normSq b :=
    boundary.normSq_pos_of_ne_zero b hb
  have hmulPos : 0 < boundary.surface.normSq (boundary.surface.mul a b) := by
    rw [boundary.normSqMultiplicative]
    exact mul_pos haPos hbPos
  have hzeroNorm :
      boundary.surface.normSq (boundary.surface.mul a b) = 0 := by
    simpa [hmul] using boundary.zero_normSq
  rw [hzeroNorm] at hmulPos
  exact (lt_irrefl (0 : ℝ)) hmulPos

/-- Slot 3 as a single frontier proposition: existence of the logical boundary. -/
def Slot3DivisionFromNormSqLogic
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (DivisionFromNormSqLogicBoundary
    (Cell := Cell) (T := T) X)

def slot3DivisionConclusionRemainingResearch :
    DivisionConclusionRemainingResearch (Cell := Cell) (T := T) where
  canonicalNormSqImpliesDivision :=
    Slot3DivisionFromNormSqLogic (Cell := Cell) (T := T)

structure Slot3DivisionFromNormSqLogicSeed
    (X : CayleyDicksonSource Cell T) where
  closedScaffold : DivisionConclusionScaffoldSeed X
  closedScaffold_eq : closedScaffold = divisionConclusionScaffoldSeedOf X


def slot3DivisionFromNormSqLogicSeedOf
    (X : CayleyDicksonSource Cell T) :
    Slot3DivisionFromNormSqLogicSeed X where
  closedScaffold := divisionConclusionScaffoldSeedOf X
  closedScaffold_eq := rfl

theorem slot3Boundary_implies_frontier
    (X : CayleyDicksonSource Cell T)
    (h : Slot3DivisionFromNormSqLogic (Cell := Cell) (T := T) X) :
    DivisionFromNormSqLogicFrontier
      slot3DivisionConclusionRemainingResearch X := by
  exact h

theorem slot3Frontier_implies_boundary
    (X : CayleyDicksonSource Cell T)
    (h : DivisionFromNormSqLogicFrontier
      slot3DivisionConclusionRemainingResearch X) :
    Slot3DivisionFromNormSqLogic (Cell := Cell) (T := T) X := by
  exact h

theorem slot3_iff_boundary
    (X : CayleyDicksonSource Cell T) :
    DivisionFromNormSqLogicFrontier
      slot3DivisionConclusionRemainingResearch X ↔
      Slot3DivisionFromNormSqLogic (Cell := Cell) (T := T) X := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem slot2_and_slot3_imply_divisionConclusionFrontier
    (X : CayleyDicksonSource Cell T)
    (h2 : SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X)
    (h3 : DivisionFromNormSqLogicFrontier
      slot3DivisionConclusionRemainingResearch X) :
    DivisionConclusionFrontier
      slot2NormSqMultiplicativityRemainingResearch
      slot3DivisionConclusionRemainingResearch
      X := by
  exact ⟨divisionConclusionScaffoldCandidate_closed X, h2, h3⟩

theorem slot3DivisionFromNormSqLogicSeed_scaffold
    (X : CayleyDicksonSource Cell T) :
    DivisionConclusionScaffoldCandidate X := by
  exact (slot3DivisionFromNormSqLogicSeedOf X).closedScaffold.scaffold

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
