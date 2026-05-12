import CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups
import CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema

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

structure S6ResearchProgram
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) where
  theoremLayer : S6TheoremLayer X
  theoremLayer_eq : theoremLayer = s6_theorem_layer X
  conjectureLayer : S6ConjectureLayer X
  conjectureLayer_eq : conjectureLayer = schema.toConjectureLayer X
  openProofObligations : S6OpenProofObligations X
  openProofObligations_eq : openProofObligations = schema.toOpenProofObligations X
  hurwitzStop : HurwitzStopSeed X
  hurwitzStop_eq : hurwitzStop = schema.toHurwitzStopSeed X

def researchProgramOf
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    S6ResearchProgram schema X where
  theoremLayer := s6_theorem_layer X
  theoremLayer_eq := rfl
  conjectureLayer := schema.toConjectureLayer X
  conjectureLayer_eq := rfl
  openProofObligations := schema.toOpenProofObligations X
  openProofObligations_eq := rfl
  hurwitzStop := schema.toHurwitzStopSeed X
  hurwitzStop_eq := rfl

def S6ResearchProgramClosed
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : Prop :=
  schema.ResearchReady X ∧ HurwitzStopClosed (schema.toHurwitzStopSeed X)

theorem threeProofDutiesClosed_implies_octonionicIdealConjecture
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : ThreeProofDutiesClosed (schema.toHurwitzStopSeed X)) :
    (schema.toConjectureLayer X).octonionicIdeal := by
  refine ⟨?_, ?_⟩
  · exact (s6_theorem_layer X).onticPrimacy
  · exact canonicalIdealAlgebraizationDuty_implies_canonicalIdealAlgebraization h.1

theorem threeProofDutiesClosed_implies_approximantProjectionConjecture
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : ThreeProofDutiesClosed (schema.toHurwitzStopSeed X)) :
    (schema.toConjectureLayer X).approximantProjection := by
  refine ⟨?_, ?_, ?_⟩
  · exact (s6_theorem_layer X).onticPrimacy
  · exact (s6_theorem_layer X).prenumericSector
  · exact h.2.1

theorem threeProofDutiesClosed_implies_cayleyDicksonLiftConjecture
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : ThreeProofDutiesClosed (schema.toHurwitzStopSeed X)) :
    (schema.toConjectureLayer X).cayleyDicksonLift := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (s6_theorem_layer X).onticPrimacy
  · exact (s6_theorem_layer X).prenumericSector
  · exact (s6_theorem_layer X).scalarAxisStatusSeparation
  · exact h.2.2

theorem threeProofDutiesClosed_implies_researchReady
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : ThreeProofDutiesClosed (schema.toHurwitzStopSeed X)) :
    schema.ResearchReady X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (s6_theorem_layer X).onticPrimacy
  · exact (s6_theorem_layer X).prenumericSector
  · exact (s6_theorem_layer X).scalarAxisStatusSeparation
  · exact threeProofDutiesClosed_implies_octonionicIdealConjecture schema X h
  · exact threeProofDutiesClosed_implies_approximantProjectionConjecture schema X h
  · exact threeProofDutiesClosed_implies_cayleyDicksonLiftConjecture schema X h

theorem hurwitzStopClosed_implies_researchReady
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : HurwitzStopClosed (schema.toHurwitzStopSeed X)) :
    schema.ResearchReady X := by
  exact threeProofDutiesClosed_implies_researchReady schema X
    (hurwitzStopClosed_implies_threeProofDutiesClosed h)

theorem hurwitzStopClosed_implies_researchProgramClosed
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : HurwitzStopClosed (schema.toHurwitzStopSeed X)) :
    S6ResearchProgramClosed schema X := by
  refine ⟨?_, h⟩
  exact hurwitzStopClosed_implies_researchReady schema X h

theorem researchProgramClosed_implies_hurwitzStopClosed
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T)
    (h : S6ResearchProgramClosed schema X) :
    HurwitzStopClosed (schema.toHurwitzStopSeed X) := by
  exact h.2

theorem researchProgramClosed_iff_hurwitzStopClosed
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    S6ResearchProgramClosed schema X ↔
      HurwitzStopClosed (schema.toHurwitzStopSeed X) := by
  constructor
  · intro h
    exact researchProgramClosed_implies_hurwitzStopClosed schema X h
  · intro h
    exact hurwitzStopClosed_implies_researchProgramClosed schema X h

theorem researchProgramOf_theoremLayer
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (researchProgramOf schema X).theoremLayer = s6_theorem_layer X := by
  rfl

theorem researchProgramOf_hurwitzStop
    (schema : S6ResearchSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (researchProgramOf schema X).hurwitzStop = schema.toHurwitzStopSeed X := by
  rfl

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
