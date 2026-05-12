import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate

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

/-- Slot 1 specialized to the exact full-alternative-law boundary frontier. -/
def slot1AlternativeLawRemainingResearch :
    AlternativeLawRemainingResearch (Cell := Cell) (T := T) where
  twoGeneratedAssociativityLift :=
    FullAlternativeLawClosureFrontier (Cell := Cell) (T := T)

structure Slot1AlternativeLawSeed
    (X : CayleyDicksonSource Cell T) where
  scaffold : AlternativeLawScaffoldSeed X
  scaffold_eq : scaffold = alternativeLawScaffoldSeedOf X


def slot1AlternativeLawSeedOf
    (X : CayleyDicksonSource Cell T) :
    Slot1AlternativeLawSeed X where
  scaffold := alternativeLawScaffoldSeedOf X
  scaffold_eq := rfl

theorem fullAlternativeLawClosureFrontier_implies_slot1
    (X : CayleyDicksonSource Cell T)
    (h : FullAlternativeLawClosureFrontier (Cell := Cell) (T := T) X) :
    AlternativeLawFromScaffold slot1AlternativeLawRemainingResearch X := by
  exact (alternativeLawFromScaffold_iff
    (remaining := slot1AlternativeLawRemainingResearch) X).2 h

theorem slot1_implies_fullAlternativeLawClosureFrontier
    (X : CayleyDicksonSource Cell T)
    (h : AlternativeLawFromScaffold slot1AlternativeLawRemainingResearch X) :
    FullAlternativeLawClosureFrontier (Cell := Cell) (T := T) X := by
  exact (alternativeLawFromScaffold_iff
    (remaining := slot1AlternativeLawRemainingResearch) X).1 h

theorem slot1_iff_fullAlternativeLawClosureFrontier
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawFromScaffold slot1AlternativeLawRemainingResearch X ↔
      FullAlternativeLawClosureFrontier (Cell := Cell) (T := T) X := by
  exact alternativeLawFromScaffold_iff
    (remaining := slot1AlternativeLawRemainingResearch) X

theorem slot1AlternativeLawSeed_scaffold
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawScaffoldCandidate X := by
  exact (slot1AlternativeLawSeedOf X).scaffold.scaffold


theorem fullAlternativeLawClosureFrontier_closed
    (X : CayleyDicksonSource Cell T) :
    FullAlternativeLawClosureFrontier (Cell := Cell) (T := T) X := by
  exact canonicalProductAlternativeLawFrontier_implies_fullAlternativeLawClosureFrontier X
    (canonicalProductAlternativeLawFrontier_closed X)

theorem slot1_closed
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawFromScaffold slot1AlternativeLawRemainingResearch X := by
  exact fullAlternativeLawClosureFrontier_implies_slot1 X
    (fullAlternativeLawClosureFrontier_closed X)

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
