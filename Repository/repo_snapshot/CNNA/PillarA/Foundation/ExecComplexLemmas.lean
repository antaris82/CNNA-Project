import CNNA.PillarA.Foundation.ExecComplex

set_option autoImplicit false

namespace CNNA.PillarA.Foundation
namespace ExecComplex

theorem eta (z : ExecComplex) : ⟨z.re, z.im⟩ = z := by
  cases z
  rfl

theorem eq_iff_re_im_eq {z w : ExecComplex} : z = w ↔ z.re = w.re ∧ z.im = w.im := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · intro h
    exact ext h.1 h.2

theorem toPair_zero : (0 : ExecComplex).toPair = (0, 0) := by
  rfl

theorem toPair_one : (1 : ExecComplex).toPair = (1, 0) := by
  rfl

theorem toPair_add (z w : ExecComplex) :
    (z + w).toPair = (z.re + w.re, z.im + w.im) := by
  rfl

theorem toPair_neg (z : ExecComplex) :
    (-z).toPair = (-z.re, -z.im) := by
  rfl

theorem toPair_sub (z w : ExecComplex) :
    (z - w).toPair = (z.re - w.re, z.im - w.im) := by
  apply Prod.ext
  · exact sub_re z w
  · exact sub_im z w

theorem toPair_mul (z w : ExecComplex) :
    (z * w).toPair =
      (z.re * w.re - z.im * w.im,
        z.re * w.im + z.im * w.re) := by
  rfl

theorem toPair_star (z : ExecComplex) :
    (star z).toPair = (z.re, -z.im) := by
  rfl

theorem mul_ofRat_left (q : ℚ) (z : ExecComplex) :
    ofRat q * z = ⟨q * z.re, q * z.im⟩ := by
  apply ext
  · change q * z.re - 0 * z.im = q * z.re
    ring
  · change q * z.im + 0 * z.re = q * z.im
    ring

theorem mul_ofRat_right (z : ExecComplex) (q : ℚ) :
    z * ofRat q = ⟨z.re * q, z.im * q⟩ := by
  apply ext
  · change z.re * q - z.im * 0 = z.re * q
    ring
  · change z.re * 0 + z.im * q = z.im * q
    ring

theorem ofRat_mul_ofRat (q r : ℚ) :
    ofRat q * ofRat r = ofRat (q * r) := by
  apply ext
  · change q * r - 0 * 0 = q * r
    ring
  · change q * 0 + 0 * r = 0
    ring

end ExecComplex

end CNNA.PillarA.Foundation
