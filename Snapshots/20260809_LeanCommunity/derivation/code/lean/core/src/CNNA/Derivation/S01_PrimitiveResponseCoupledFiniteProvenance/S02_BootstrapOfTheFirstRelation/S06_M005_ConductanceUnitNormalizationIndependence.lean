import Init.Data.Rat.Lemmas
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S03_N001_InitialConductanceNormalizationCStar1

/-!
Paper 1.2.6 / M005 — conductance-unit normalization independence.

N001 fixes the canonical representative C★ = 1.  M005 proves that this does
not add a third physical input: positive rational changes of conductance unit
change only the representative of a normalized scalar response.

Python evaluates the quotient exactly with rational arithmetic.  Lean uses the
cross-product characterization, so no division is required in the theorem.
The unit-change variable is a proof/comparison variable, not a CNNA input.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

/-- Equality of normalized scalar responses, stated without division. -/
def SameNormalizedResponse
    (response unit response' unit' : Rat) : Prop :=
  response * unit' = response' * unit

/-- The fixed N001 numeral `1`, embedded into the rational unit carrier. -/
def n001ConductanceUnit (normalization : InitialConductanceNormalization) : Rat :=
  (InitialConductanceNormalization.value normalization : Rat)

/-- The N001 rational representative is exactly one. -/
theorem n001ConductanceUnit_eq_one
    (normalization : InitialConductanceNormalization) :
    n001ConductanceUnit normalization = 1 := by
  change ((1 : Nat) : Rat) = 1
  exact Rat.natCast_ofNat

/--
A common positive rational rescaling preserves the normalized response.
Positivity identifies the transformation as an admissible unit change; the
algebraic identity itself is the cross-product equality below.
-/
theorem commonPositiveRescalingPreservesNormalizedResponse
    (response unit scale : Rat)
    (_scalePositive : 0 < scale) :
    SameNormalizedResponse response unit (scale * response) (scale * unit) := by
  unfold SameNormalizedResponse
  calc
    response * (scale * unit) = (response * scale) * unit :=
      (Rat.mul_assoc response scale unit).symm
    _ = (scale * response) * unit := by
      exact congrArg (fun x : Rat => x * unit) (Rat.mul_comm response scale)

/--
Every positive rational conductance unit represents the same normalized datum
as the N001 canonical unit `1` when the response coordinate is rescaled with
that unit.  Thus N001 selects a representative of a unit-equivalence class;
the alternative unit is not an additional CNNA model input.
-/
theorem n001CanonicalRepresentativeForPositiveUnit
    (normalization : InitialConductanceNormalization)
    (normalizedValue unit : Rat)
    (_unitPositive : 0 < unit) :
    SameNormalizedResponse
      normalizedValue
      (n001ConductanceUnit normalization)
      (unit * normalizedValue)
      unit := by
  rw [n001ConductanceUnit_eq_one normalization]
  unfold SameNormalizedResponse
  calc
    normalizedValue * unit = unit * normalizedValue :=
      Rat.mul_comm normalizedValue unit
    _ = (unit * normalizedValue) * 1 :=
      (Rat.mul_one (unit * normalizedValue)).symm

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
