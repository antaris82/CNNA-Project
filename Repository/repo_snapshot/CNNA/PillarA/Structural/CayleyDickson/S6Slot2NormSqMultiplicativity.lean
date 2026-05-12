import CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition

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

/-- Closed product/norm surface for the honest implementation of Slot 2. -/
structure CanonicalNormSqProductSurface
    (X : CayleyDicksonSource Cell T) where
  Carrier : Type u
  mul : Carrier → Carrier → Carrier
  normSq : Carrier → ℝ

/--
Boundary object for Slot 2: the already closed scaffold together with a canonical
product/norm surface, embeddings of the triadic blocks, a lift of the diagonal
norm controls, and norm-square multiplicativity on the canonical product.
-/
structure SchurBlockNormSqMultiplicativityBoundary
    (X : CayleyDicksonSource Cell T) where
  scaffold : NormSqMultiplicativityScaffoldSeed X
  surface : CanonicalNormSqProductSurface (Cell := Cell) (T := T) X
  embedOuter : ∀ κ η : ReducedRoleIndex,
    TriadicOuterBlock X κ η → surface.Carrier
  embedCenter : TriadicCenterBlock X → surface.Carrier
  liftDiagonalToCanonicalNormSq : Prop
  normSqMultiplicativeOnCanonicalProduct :
    ∀ a b : surface.Carrier,
      surface.normSq (surface.mul a b) =
        surface.normSq a * surface.normSq b

/-- Slot 2 as a single frontier proposition: existence of the boundary object. -/
def Slot2NormSqMultiplicativity
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (SchurBlockNormSqMultiplicativityBoundary
    (Cell := Cell) (T := T) X)

def slot2NormSqMultiplicativityRemainingResearch :
    NormSqMultiplicativityRemainingResearch (Cell := Cell) (T := T) where
  liftDiagonalToCanonicalNormSq :=
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T)
  normSqMultiplicativeOnCanonicalProduct :=
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T)

structure Slot2NormSqMultiplicativitySeed
    (X : CayleyDicksonSource Cell T) where
  scaffold : NormSqMultiplicativityScaffoldSeed X
  scaffold_eq : scaffold = normSqMultiplicativityScaffoldSeedOf X


def slot2NormSqMultiplicativitySeedOf
    (X : CayleyDicksonSource Cell T) :
    Slot2NormSqMultiplicativitySeed X where
  scaffold := normSqMultiplicativityScaffoldSeedOf X
  scaffold_eq := rfl

theorem slot2Boundary_implies_frontier
    (X : CayleyDicksonSource Cell T)
    (h : Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X) :
    SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X := by
  exact ⟨normSqMultiplicativityScaffoldCandidate_closed X, h, h⟩

theorem slot2Frontier_implies_boundary
    (X : CayleyDicksonSource Cell T)
    (h : SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X) :
    Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X := by
  exact h.2.1

theorem slot2_iff_boundary
    (X : CayleyDicksonSource Cell T) :
    SchurBlockNormSqMultiplicativityFrontier
      slot2NormSqMultiplicativityRemainingResearch X ↔
      Slot2NormSqMultiplicativity (Cell := Cell) (T := T) X := by
  constructor
  · intro h
    exact slot2Frontier_implies_boundary X h
  · intro h
    exact slot2Boundary_implies_frontier X h

theorem slot2NormSqMultiplicativitySeed_scaffold
    (X : CayleyDicksonSource Cell T) :
    NormSqMultiplicativityScaffoldCandidate X := by
  exact (slot2NormSqMultiplicativitySeedOf X).scaffold.scaffold

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
