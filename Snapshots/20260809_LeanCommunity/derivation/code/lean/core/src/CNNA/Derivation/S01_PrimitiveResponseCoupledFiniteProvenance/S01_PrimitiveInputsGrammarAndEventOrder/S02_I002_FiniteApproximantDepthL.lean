/-!
Paper 1.1.2 / I002 — finite approximant depth `L`.

Scientific contract:
* `L` is a free finite-depth input;
* `L : Nat`, hence `L` is nonnegative;
* `0` is admissible;
* no default value and no infinity sentinel are introduced here;
* `L` is a terminal provenance-depth cutoff, not a spatial coordinate.

Unlike I001, no extra proof field is needed: Lean's `Nat` already carries
exactly the nonnegative-integer domain required by this node.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- The free finite approximant depth `L`. -/
structure FiniteApproximantDepth where
  value : Nat

namespace FiniteApproximantDepth

/-- Explicit constructor equation used at module boundaries. -/
theorem mk_value (value : Nat) :
    (FiniteApproximantDepth.mk value).value = value :=
  rfl

/-- The lower boundary `L = 0` is a valid inhabitant, not a sentinel. -/
theorem zeroAdmissible : ∃ L : FiniteApproximantDepth, L.value = 0 :=
  ⟨FiniteApproximantDepth.mk 0, rfl⟩

end FiniteApproximantDepth

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
