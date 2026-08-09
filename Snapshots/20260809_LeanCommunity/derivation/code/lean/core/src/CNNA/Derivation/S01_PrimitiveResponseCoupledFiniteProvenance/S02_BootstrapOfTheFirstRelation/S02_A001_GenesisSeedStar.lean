/-!
Paper 1.2.2 / A001 — genesis seed `★`.

A001 is a technical singleton token used only by the downstream bootstrap
construction C013.  It carries no numerical, geometric, dynamical,
conductance, timing, address, or response information and is not a model input.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

/-- The information-free bootstrap seed has exactly one constructor. -/
inductive GenesisSeed : Type where
  | star

namespace GenesisSeed

/-- Canonical A001 seed token. -/
def canonical : GenesisSeed := .star

/-- Every A001 seed value is the canonical singleton token. -/
theorem eqCanonical (s : GenesisSeed) : s = canonical := by
  cases s
  rfl

end GenesisSeed

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
