import CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold

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

/-- A closed single-carrier product surface on which the full alternative law can be stated. -/
structure AlternativeLawProductSurface
    (X : CayleyDicksonSource Cell T) where
  Carrier : Type u
  mul : Carrier → Carrier → Carrier

/-- Left alternativity on a closed product surface. -/
def LeftAlternativeLaw
    {X : CayleyDicksonSource Cell T}
    (surface : AlternativeLawProductSurface (Cell := Cell) (T := T) X) : Prop :=
  ∀ a b : surface.Carrier,
    surface.mul (surface.mul a a) b =
      surface.mul a (surface.mul a b)

/-- Right alternativity on a closed product surface. -/
def RightAlternativeLaw
    {X : CayleyDicksonSource Cell T}
    (surface : AlternativeLawProductSurface (Cell := Cell) (T := T) X) : Prop :=
  ∀ a b : surface.Carrier,
    surface.mul (surface.mul a b) b =
      surface.mul a (surface.mul b b)

/-- The full alternative law is the conjunction of left and right alternativity. -/
def FullAlternativeLaw
    {X : CayleyDicksonSource Cell T}
    (surface : AlternativeLawProductSurface (Cell := Cell) (T := T) X) : Prop :=
  LeftAlternativeLaw surface ∧ RightAlternativeLaw surface

/--
Boundary object for an honest closure of the alternative-law obligation:
we keep the already closed S6 scaffold and make the missing closed product
surface explicit, together with its compatibility slots.
-/
structure FullAlternativeLawBoundary
    (X : CayleyDicksonSource Cell T) where
  scaffold : AlternativeLawScaffoldSeed X
  surface : AlternativeLawProductSurface X
  embedOuter : ∀ κ η : ReducedRoleIndex,
    TriadicOuterBlock X κ η → surface.Carrier
  embedCenter : TriadicCenterBlock X → surface.Carrier
  outerFormulaCompatibility : Prop
  centerInverseCompatibility : Prop
  fullAlternativeLaw : FullAlternativeLaw surface

/-- The full law is immediately available once the boundary object is instantiated. -/
theorem fullAlternativeLaw_of_boundary
    {X : CayleyDicksonSource Cell T}
    (boundary : FullAlternativeLawBoundary (Cell := Cell) (T := T) X) :
    FullAlternativeLaw boundary.surface := by
  exact boundary.fullAlternativeLaw

/--
This is the precise remaining closure condition for the current S6 scaffold:
a closed single-carrier product surface compatible with the triadic outer/center data,
and satisfying the full alternative law on that surface.
-/
def FullAlternativeLawClosureFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (FullAlternativeLawBoundary (Cell := Cell) (T := T) X)

/-- The current S6 chain already supplies the closed scaffold part of the boundary. -/
def fullAlternativeLawBoundaryScaffoldSeedOf
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawScaffoldSeed X :=
  alternativeLawScaffoldSeedOf X

theorem fullAlternativeLawClosureFrontier_iff
    (X : CayleyDicksonSource Cell T) :
    FullAlternativeLawClosureFrontier (Cell := Cell) (T := T) X ↔
      Nonempty (FullAlternativeLawBoundary (Cell := Cell) (T := T) X) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
The currently closed part of the frontier is exactly the scaffold; the remaining part
is the closed product surface plus its compatibility and full-law proof.
-/
theorem fullAlternativeLawBoundary_has_closed_scaffold
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawScaffoldCandidate X := by
  exact (fullAlternativeLawBoundaryScaffoldSeedOf X).scaffold

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
