import CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification

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

structure AlternativeLawScaffoldCandidate
    (X : CayleyDicksonSource Cell T) : Prop where
  leftSelfFormula :
    triadicOuterSchur X .left .left =
      triadicOuterRawBlock X .left .left -
        triadicOuterMediated X .left .left
  leftRightFormula :
    triadicOuterSchur X .left .right =
      triadicOuterRawBlock X .left .right -
        triadicOuterMediated X .left .right
  rightLeftFormula :
    triadicOuterSchur X .right .left =
      triadicOuterRawBlock X .right .left -
        triadicOuterMediated X .right .left
  rightSelfFormula :
    triadicOuterSchur X .right .right =
      triadicOuterRawBlock X .right .right -
        triadicOuterMediated X .right .right
  dualCompatibleConjugation : DualCompatibleConjugationCandidate

theorem alternativeLawScaffoldCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawScaffoldCandidate X := by
  have hTri := canonicalTriadicMultiplicationCandidate_of_octonionic X
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hTri.1 .left .left
  · exact hTri.1 .left .right
  · exact hTri.1 .right .left
  · exact hTri.1 .right .right
  · exact dualCompatibleConjugationCandidate_closed

structure AlternativeLawScaffoldSeed
    (X : CayleyDicksonSource Cell T) where
  cayleyDickson : CayleyDicksonIdentificationSeed X
  cayleyDickson_eq : cayleyDickson = cayleyDicksonIdentificationSeedOf X
  scaffold : AlternativeLawScaffoldCandidate X

def alternativeLawScaffoldSeedOf
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawScaffoldSeed X where
  cayleyDickson := cayleyDicksonIdentificationSeedOf X
  cayleyDickson_eq := rfl
  scaffold := alternativeLawScaffoldCandidate_closed X

structure AlternativeLawRemainingResearch where
  twoGeneratedAssociativityLift : CayleyDicksonSource Cell T → Prop

def AlternativeLawFromScaffold
    (remaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  AlternativeLawScaffoldCandidate X ∧
    remaining.twoGeneratedAssociativityLift X

theorem alternativeLawFromScaffold_iff
    (remaining : AlternativeLawRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawFromScaffold remaining X ↔
      remaining.twoGeneratedAssociativityLift X := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨alternativeLawScaffoldCandidate_closed X, h⟩

theorem alternativeLawScaffoldSeed_scaffold
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawScaffoldCandidate X := by
  exact (alternativeLawScaffoldSeedOf X).scaffold

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
