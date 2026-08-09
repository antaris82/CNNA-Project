import Init.Data.List.Pairwise
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S01_C005_ResponseCapableStateSchemaXnNGe1

/-!
C005 generic list closure used by recurrent successors.

These lemmas know nothing about M004 support.  They state only how the C005
ordered-pair uniqueness and `HasConductance` predicates behave under append.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

namespace ResponseCapableState

/-- An already-born carrier node remains born when the non-root list is
extended on the right. -/
theorem nodeBorn_append_left {G : FiniteBAryProvenanceGrammar}
    {oldBorn newBorn : List (ProvenanceAddress G.branching)}
    {a : ProvenanceAddress G.branching}
    (h : NodeBorn G oldBorn a) : NodeBorn G (oldBorn ++ newBorn) a := by
  cases h with
  | inl hRoot =>
      exact Or.inl hRoot
  | inr hOld =>
      exact Or.inr ((List.mem_append).2 (Or.inl hOld))

/-- Every explicitly appended non-root node belongs to the extended carrier. -/
theorem nodeBorn_append_right {G : FiniteBAryProvenanceGrammar}
    {oldBorn newBorn : List (ProvenanceAddress G.branching)}
    {a : ProvenanceAddress G.branching}
    (h : a ∈ newBorn) : NodeBorn G (oldBorn ++ newBorn) a := by
  exact Or.inr ((List.mem_append).2 (Or.inr h))

/-- Pairwise C005 ordered-pair uniqueness is closed under append when both
pieces are internally unique and every old/new ordered pair is distinct. -/
theorem conductancePairsUnique_append {b : BranchingParameter}
    {oldEdges newEdges : List (DirectedConductance b)}
    (hOld : List.Pairwise DistinctConductancePair oldEdges)
    (hNew : List.Pairwise DistinctConductancePair newEdges)
    (hCross : ∀ oldEdge, oldEdge ∈ oldEdges →
      ∀ newEdge, newEdge ∈ newEdges →
        DistinctConductancePair oldEdge newEdge) :
    List.Pairwise DistinctConductancePair (oldEdges ++ newEdges) := by
  exact (List.pairwise_append).2 ⟨hOld, hNew, hCross⟩

/-- An old conductance remains present after appending a new block. -/
theorem hasConductance_append_left {b : BranchingParameter}
    {oldEdges newEdges : List (DirectedConductance b)}
    {source target : ProvenanceAddress b}
    (h : HasConductance oldEdges source target) :
    HasConductance (oldEdges ++ newEdges) source target := by
  obtain ⟨edge, hMem, hSource, hTarget⟩ := h
  refine ⟨edge, (List.mem_append).2 (Or.inl hMem), hSource, hTarget⟩

/-- A conductance in the appended block is present in the combined list. -/
theorem hasConductance_append_right {b : BranchingParameter}
    {oldEdges newEdges : List (DirectedConductance b)}
    {source target : ProvenanceAddress b}
    (h : HasConductance newEdges source target) :
    HasConductance (oldEdges ++ newEdges) source target := by
  obtain ⟨edge, hMem, hSource, hTarget⟩ := h
  refine ⟨edge, (List.mem_append).2 (Or.inr hMem), hSource, hTarget⟩

end ResponseCapableState

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
