import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import CNNA.PillarA.Foundation.HermitianStructure

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

structure ExecComplex where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace ExecComplex

@[ext]
theorem ext {z w : ExecComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z
  cases w
  cases hre
  cases him
  rfl

def toPair (z : ExecComplex) : ℚ × ℚ :=
  (z.re, z.im)

def ofPair (p : ℚ × ℚ) : ExecComplex :=
  ⟨p.1, p.2⟩

theorem toPair_def (z : ExecComplex) : z.toPair = (z.re, z.im) := by
  rfl

theorem ofPair_def (p : ℚ × ℚ) : ofPair p = ⟨p.1, p.2⟩ := by
  rfl

theorem ofPair_toPair (z : ExecComplex) : ofPair z.toPair = z := by
  cases z
  rfl

theorem toPair_ofPair (p : ℚ × ℚ) : (ofPair p).toPair = p := by
  cases p
  rfl

theorem toPair_injective : Function.Injective toPair := by
  intro z w h
  apply ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def equivRatProd : ExecComplex ≃ ℚ × ℚ where
  toFun := toPair
  invFun := ofPair
  left_inv := ofPair_toPair
  right_inv := toPair_ofPair

def ofRat (q : ℚ) : ExecComplex :=
  ⟨q, 0⟩

theorem ofRat_re (q : ℚ) : (ofRat q).re = q := by
  rfl

theorem ofRat_im (q : ℚ) : (ofRat q).im = 0 := by
  rfl

theorem ofRat_injective : Function.Injective ofRat := by
  intro q r h
  have hre : (ofRat q).re = (ofRat r).re := congrArg ExecComplex.re h
  exact hre

instance : Zero ExecComplex where
  zero := ⟨0, 0⟩

instance : One ExecComplex where
  one := ⟨1, 0⟩

instance : Add ExecComplex where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

instance : Neg ExecComplex where
  neg z := ⟨-z.re, -z.im⟩

instance : Sub ExecComplex where
  sub z w := z + (-w)

instance : Mul ExecComplex where
  mul z w :=
    ⟨z.re * w.re - z.im * w.im,
      z.re * w.im + z.im * w.re⟩

instance : Star ExecComplex where
  star z := ⟨z.re, -z.im⟩

theorem zero_re : (0 : ExecComplex).re = 0 := by
  rfl

theorem zero_im : (0 : ExecComplex).im = 0 := by
  rfl

theorem one_re : (1 : ExecComplex).re = 1 := by
  rfl

theorem one_im : (1 : ExecComplex).im = 0 := by
  rfl

theorem add_re (z w : ExecComplex) : (z + w).re = z.re + w.re := by
  rfl

theorem add_im (z w : ExecComplex) : (z + w).im = z.im + w.im := by
  rfl

theorem neg_re (z : ExecComplex) : (-z).re = -z.re := by
  rfl

theorem neg_im (z : ExecComplex) : (-z).im = -z.im := by
  rfl

theorem sub_re (z w : ExecComplex) : (z - w).re = z.re - w.re := by
  change z.re + (-w.re) = z.re - w.re
  exact (sub_eq_add_neg _ _).symm

theorem sub_im (z w : ExecComplex) : (z - w).im = z.im - w.im := by
  change z.im + (-w.im) = z.im - w.im
  exact (sub_eq_add_neg _ _).symm

theorem mul_re (z w : ExecComplex) : (z * w).re = z.re * w.re - z.im * w.im := by
  rfl

theorem mul_im (z w : ExecComplex) : (z * w).im = z.re * w.im + z.im * w.re := by
  rfl

theorem star_re (z : ExecComplex) : (star z).re = z.re := by
  rfl

theorem star_im (z : ExecComplex) : (star z).im = -z.im := by
  rfl

theorem add_assoc (a b c : ExecComplex) : a + b + c = a + (b + c) := by
  apply ext
  · change (a.re + b.re) + c.re = a.re + (b.re + c.re)
    exact _root_.add_assoc _ _ _
  · change (a.im + b.im) + c.im = a.im + (b.im + c.im)
    exact _root_.add_assoc _ _ _

theorem zero_add (a : ExecComplex) : 0 + a = a := by
  apply ext
  · change 0 + a.re = a.re
    exact _root_.zero_add _
  · change 0 + a.im = a.im
    exact _root_.zero_add _

theorem neg_add_cancel (a : ExecComplex) : -a + a = 0 := by
  apply ext
  · change -a.re + a.re = 0
    exact _root_.neg_add_cancel _
  · change -a.im + a.im = 0
    exact _root_.neg_add_cancel _

theorem mul_assoc (a b c : ExecComplex) : a * b * c = a * (b * c) := by
  apply ext
  · change
      ((a.re * b.re - a.im * b.im) * c.re - (a.re * b.im + a.im * b.re) * c.im) =
        (a.re * (b.re * c.re - b.im * c.im) - a.im * (b.re * c.im + b.im * c.re))
    ring
  · change
      ((a.re * b.re - a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re) =
        (a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re - b.im * c.im))
    ring

theorem mul_comm (a b : ExecComplex) : a * b = b * a := by
  apply ext
  · change a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im
    ring
  · change a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re
    ring

theorem one_mul (a : ExecComplex) : 1 * a = a := by
  apply ext
  · change 1 * a.re - 0 * a.im = a.re
    ring
  · change 1 * a.im + 0 * a.re = a.im
    ring

theorem left_distrib (a b c : ExecComplex) : a * (b + c) = a * b + a * c := by
  apply ext
  · change a.re * (b.re + c.re) - a.im * (b.im + c.im) =
      (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im)
    ring
  · change a.re * (b.im + c.im) + a.im * (b.re + c.re) =
      (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re)
    ring

instance : CommRing ExecComplex :=
  CommRing.ofMinimalAxioms
    add_assoc
    zero_add
    neg_add_cancel
    mul_assoc
    mul_comm
    one_mul
    left_distrib

instance : StarRing ExecComplex where
  star := fun z => ⟨z.re, -z.im⟩
  star_involutive := by
    intro z
    apply ext
    · rfl
    · exact neg_neg z.im
  star_mul := by
    intro z w
    apply ext
    · change z.re * w.re - z.im * w.im = w.re * z.re - (-w.im) * (-z.im)
      ring
    · change -(z.re * w.im + z.im * w.re) = w.re * (-z.im) + (-w.im) * z.re
      ring
  star_add := by
    intro z w
    apply ext
    · rfl
    · change -(z.im + w.im) = -z.im + -w.im
      exact neg_add _ _

theorem star_def (z : ExecComplex) : star z = ⟨z.re, -z.im⟩ := by
  rfl

theorem star_star (z : ExecComplex) : star (star z) = z := by
  apply ext
  · rfl
  · exact neg_neg z.im

theorem star_add (z w : ExecComplex) : star (z + w) = star z + star w := by
  apply ext
  · rfl
  · change -(z.im + w.im) = -z.im + -w.im
    exact neg_add _ _

theorem star_mul (z w : ExecComplex) : star (z * w) = star w * star z := by
  apply ext
  · change z.re * w.re - z.im * w.im = w.re * z.re - (-w.im) * (-z.im)
    ring
  · change -(z.re * w.im + z.im * w.re) = w.re * (-z.im) + (-w.im) * z.re
    ring

theorem star_ofRat (q : ℚ) : star (ofRat q) = ofRat q := by
  apply ext
  · rfl
  · exact neg_zero

instance instSeedScalarExecComplex : SeedScalar ExecComplex where
  toCommRing := inferInstance
  toStarRing := inferInstance

end ExecComplex

end CNNA.PillarA.Foundation
