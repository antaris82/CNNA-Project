import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S03_C006_BirthLocalSchurDtnPrimitive

/-!
C006 successor closure — canonical rational realization of `ExactFraction`.

T002 must re-enter the C005 schema, whose conductance carrier is `Rat`, while
M004/C016/C017 carry C006 `ExactFraction` values.  The conversion and its
representation/positivity facts belong to C006, not to T002.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

namespace BirthLocalSchurDtnPrimitive
namespace ExactFraction

/-- Canonical rational value represented by one exact fraction.  `Rat.divInt`
is a Core operation; no mathlib rational constructor is required here. -/
def toRat (raw : ExactFraction) : Rat :=
  Rat.divInt raw.num (Int.ofNat raw.den)

/-- `SameValue` has exactly the intended rational semantics. -/
theorem toRat_eq_of_sameValue {left right : ExactFraction}
    (h : SameValue left right) : toRat left = toRat right := by
  unfold toRat
  exact (Rat.divInt_eq_divInt_iff
    (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt left.denPos))
    (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt right.denPos))).2 h

/-- Equality of the canonical rational realizations reflects C006 value
equality as well. -/
theorem sameValue_of_toRat_eq {left right : ExactFraction}
    (h : toRat left = toRat right) : SameValue left right := by
  unfold toRat at h
  exact (Rat.divInt_eq_divInt_iff
    (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt left.denPos))
    (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt right.denPos))).1 h

/-- Canonical C006 encoding decodes back to the original rational. -/
theorem toRat_ofRat (q : Rat) : toRat (ofRat q) = q := by
  unfold toRat ofRat
  exact Rat.num_divInt_den q

/-- Every exact fraction represents its own canonical rational realization. -/
theorem toRat_represents (raw : ExactFraction) : Represents raw (toRat raw) := by
  unfold Represents
  apply sameValue_of_toRat_eq
  exact (toRat_ofRat (toRat raw)).symm

/-- Positive C006 numerator plus positive denominator yields a nonnegative C005
rational conductance. -/
theorem toRat_nonneg_of_num_nonneg {raw : ExactFraction}
    (hNum : 0 ≤ raw.num) : 0 ≤ toRat raw := by
  unfold toRat
  have hDenPos : 0 < Int.ofNat raw.den :=
    (Int.natCast_pos).2 raw.denPos
  exact (Rat.divInt_nonneg_iff_of_pos_right hDenPos).2 hNum

/-- Positive C006 numerator plus positive denominator yields a positive C005
rational conductance. -/
theorem toRat_pos_of_num_pos {raw : ExactFraction}
    (hNum : 0 < raw.num) : 0 < toRat raw := by
  have hNumNonneg : 0 ≤ raw.num := by
    omega
  have hNonneg : 0 ≤ toRat raw :=
    toRat_nonneg_of_num_nonneg hNumNonneg
  apply Rat.lt_of_le_of_ne hNonneg
  intro hZero
  have hDenNe : Int.ofNat raw.den ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt raw.denPos)
  have hOneNe : (1 : Int) ≠ 0 := by
    omega
  have hDivEq :
      Rat.divInt 0 1 = Rat.divInt raw.num (Int.ofNat raw.den) := by
    rw [Rat.zero_divInt]
    exact hZero
  have hCross := (Rat.divInt_eq_divInt_iff hOneNe hDenNe).1 hDivEq
  rw [Int.zero_mul, Int.mul_one] at hCross
  have hNumZero : raw.num = 0 := hCross.symm
  omega

end ExactFraction
end BirthLocalSchurDtnPrimitive

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
