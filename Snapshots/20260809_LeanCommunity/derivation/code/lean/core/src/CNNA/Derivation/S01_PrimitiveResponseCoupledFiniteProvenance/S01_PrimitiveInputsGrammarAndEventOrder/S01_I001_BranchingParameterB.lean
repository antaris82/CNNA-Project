/-!
Paper 1.1.1 / I001 — branching parameter `b`.

Scientific contract:
* `b` is a free structural input;
* `b : Nat`;
* `2 ≤ b`;
* no default value for `b` is introduced here.

The lower-bound proof is stored in the carrier itself so downstream modules,
in particular C003, do not rely on an untracked side condition.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- The free branching input `b`, together with its exact admissibility proof. -/
structure BranchingParameter where
  value : Nat
  ge_two : 2 ≤ value

namespace BranchingParameter

/-- The I001 lower bound is available by projection, not by automation. -/
theorem lowerBound (b : BranchingParameter) : 2 ≤ b.value :=
  b.ge_two

/-- Explicit constructor equation used at module boundaries. -/
theorem mk_value (value : Nat) (h : 2 ≤ value) :
    (BranchingParameter.mk value h).value = value :=
  rfl

end BranchingParameter

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
