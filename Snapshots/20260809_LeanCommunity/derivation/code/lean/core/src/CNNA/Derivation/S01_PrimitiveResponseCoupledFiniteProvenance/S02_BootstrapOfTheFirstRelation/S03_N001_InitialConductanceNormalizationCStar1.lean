/-!
Paper 1.2.3 / N001 — initial conductance normalization `C★ = 1`.

N001 is a zero-payload fixed normalization, not a free model input.  It fixes
only the unit value used later when C013 creates the first root–child
relation.  The two directed storage orientations start equal.  The local use
of the exact numeral `1 : Nat` does not choose the scalar carrier of later
conductances.  This module creates no relation and proves no unit-independence
theorem; the latter belongs to M005.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

/-- The fixed N001 convention has exactly one value and carries no parameter. -/
inductive InitialConductanceNormalization : Type where
  | unit

namespace InitialConductanceNormalization

/-- Canonical N001 normalization token. -/
def canonical : InitialConductanceNormalization := .unit

/-- Dimensionless conductance normalization `C★ = 1`. -/
def value (_ : InitialConductanceNormalization) : Nat := 1

/-- Directed storage starts with the same unit value in both orientations. -/
def directedValues (N : InitialConductanceNormalization) : Nat × Nat :=
  (value N, value N)

/-- Both directed orientations therefore start at unit conductance. -/
theorem directedValues_eq_unit_pair (N : InitialConductanceNormalization) :
    directedValues N = (1, 1) :=
  rfl

end InitialConductanceNormalization

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
