import CNNAProofs.P001.DirectedSchurDtnKronChannelClosure

/-!
# P001 — exact C006-to-mathlib rational semantics

This module is the single proof bridge from the mathlib-free C006 fraction and
matrix operations to the proof-layer rational matrix semantics.  It proves:

* exact value preservation of `ofRat`, zero, addition, multiplication, and
  subtraction;
* equivalence of C006 cross-multiplication equality with equality in `ℚ`;
* equality of C006 row-by-column matrix multiplication with the explicit
  proof-layer finite sum;
* equality of C006 matrix subtraction with proof-layer subtraction;
* the three fields of `ExactSemanticBridge` for every ordered block system.

No inverse, determinant, regularization, positivity, existence, or uniqueness
claim occurs here.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- Canonical C006 encoding has exactly its original rational value. -/
theorem exactFractionValue_ofRat (q : ℚ) :
    exactFractionValue (ExactFraction.ofRat q) = q := by
  unfold exactFractionValue ExactFraction.ofRat
  exact Rat.mkRat_self q

/-- C006 cross multiplication is precisely equality of rational values. -/
theorem sameValue_iff_exactFractionValue_eq {left right : ExactFraction} :
    ExactFraction.SameValue left right ↔
      exactFractionValue left = exactFractionValue right := by
  unfold ExactFraction.SameValue exactFractionValue
  have hLeft : left.den ≠ 0 := Nat.ne_of_gt left.denPos
  have hRight : right.den ≠ 0 := Nat.ne_of_gt right.denPos
  exact (Rat.mkRat_eq_iff hLeft hRight).symm

/-- C006 representation is equality with the encoded rational value. -/
theorem represents_iff_exactFractionValue_eq
    {raw : ExactFraction} {q : ℚ} :
    ExactFraction.Represents raw q ↔ exactFractionValue raw = q := by
  unfold ExactFraction.Represents
  rw [sameValue_iff_exactFractionValue_eq, exactFractionValue_ofRat]

/-- C006 exact zero has rational value zero. -/
theorem exactFractionValue_zero :
    exactFractionValue ExactFraction.zero = 0 := by
  unfold exactFractionValue ExactFraction.zero
  exact Rat.zero_mkRat 1

/-- C006 exact addition agrees with addition in `ℚ`. -/
theorem exactFractionValue_add (left right : ExactFraction) :
    exactFractionValue (ExactFraction.add left right) =
      exactFractionValue left + exactFractionValue right := by
  unfold exactFractionValue ExactFraction.add
  have hLeft : left.den ≠ 0 := Nat.ne_of_gt left.denPos
  have hRight : right.den ≠ 0 := Nat.ne_of_gt right.denPos
  exact (Rat.mkRat_add_mkRat left.num right.num hLeft hRight).symm

/-- C006 exact multiplication agrees with multiplication in `ℚ`. -/
theorem exactFractionValue_mul (left right : ExactFraction) :
    exactFractionValue (ExactFraction.mul left right) =
      exactFractionValue left * exactFractionValue right := by
  unfold exactFractionValue ExactFraction.mul
  exact (Rat.mkRat_mul_mkRat left.num right.num left.den right.den).symm

/-- C006 exact subtraction agrees with subtraction in `ℚ`. -/
theorem exactFractionValue_sub (left right : ExactFraction) :
    exactFractionValue (ExactFraction.sub left right) =
      exactFractionValue left - exactFractionValue right := by
  change
    _root_.mkRat
        (left.num * Int.ofNat right.den - right.num * Int.ofNat left.den)
        (left.den * right.den) =
      _root_.mkRat left.num left.den - _root_.mkRat right.num right.den
  have hLeft : left.den ≠ 0 := Nat.ne_of_gt left.denPos
  have hRight : right.den ≠ 0 := Nat.ne_of_gt right.denPos
  rw [Rat.sub_eq_add_neg, Rat.neg_mkRat]
  rw [Rat.mkRat_add_mkRat left.num (-right.num) hLeft hRight]
  exact congrArg
    (fun numerator : Int => _root_.mkRat numerator (left.den * right.den))
    (by
      rw [Int.ofNat_eq_natCast right.den]
      rw [Int.ofNat_eq_natCast left.den]
      rw [Int.neg_mul, Int.sub_eq_add_neg])

/-- Rational value commutes with a finite C006 additive fold. -/
theorem exactFractionValue_finFoldl_add {count : Nat}
    (term : Fin count → ExactFraction) (initial : ExactFraction) :
    exactFractionValue
        (Fin.foldl count
          (fun accumulator index =>
            ExactFraction.add accumulator (term index))
          initial) =
      Fin.foldl count
        (fun accumulator index =>
          accumulator + exactFractionValue (term index))
        (exactFractionValue initial) := by
  induction count generalizing initial with
  | zero =>
      rw [Fin.foldl_zero, Fin.foldl_zero]
  | succ count ih =>
      rw [Fin.foldl_succ, Fin.foldl_succ]
      rw [ih, exactFractionValue_add]

/-- A finite additive fold is its initial value plus the corresponding sum. -/
theorem finFoldl_add_eq_initial_add_sum {count : Nat}
    (term : Fin count → ℚ) (initial : ℚ) :
    Fin.foldl count (fun accumulator index => accumulator + term index) initial =
      initial + ∑ index, term index := by
  induction count generalizing initial with
  | zero =>
      rw [Fin.foldl_zero, Fin.sum_univ_zero, add_zero]
  | succ count ih =>
      rw [Fin.foldl_succ, Fin.sum_univ_succ, ih]
      ring

/-- The zero-initial finite additive fold is the corresponding finite sum. -/
theorem finFoldl_add_eq_sum {count : Nat} (term : Fin count → ℚ) :
    Fin.foldl count (fun accumulator index => accumulator + term index) 0 =
      ∑ index, term index := by
  rw [finFoldl_add_eq_initial_add_sum, zero_add]

/-- Rational value of one C006 matrix-product entry. -/
theorem exactFractionValue_matrixMul_entry {rows inner cols : Nat}
    (left : RatMatrix rows inner)
    (right : RatMatrix inner cols)
    (row : Fin rows) (column : Fin cols) :
    exactFractionValue (matrixMul left right row column) =
      ∑ index, left row index * right index column := by
  unfold matrixMul rawMatrixMul
  rw [exactFractionValue_finFoldl_add]
  rw [exactFractionValue_zero]
  rw [finFoldl_add_eq_sum]
  apply Finset.sum_congr rfl
  intro index _hIndex
  rw [exactFractionValue_mul]
  rw [exactFractionValue_ofRat, exactFractionValue_ofRat]

/-- C006 matrix multiplication has exactly the explicit rational matrix value. -/
theorem exactMatrixValue_matrixMul {rows inner cols : Nat}
    (left : RatMatrix rows inner)
    (right : RatMatrix inner cols) :
    exactMatrixValue (matrixMul left right) =
      rationalMatrixMul (coreRatMatrixValue left) (coreRatMatrixValue right) := by
  apply Matrix.ext
  intro row column
  unfold exactMatrixValue rationalMatrixMul coreRatMatrixValue
  exact exactFractionValue_matrixMul_entry left right row column

/-- C006 matrix subtraction has exactly the rational entrywise value. -/
theorem exactMatrixValue_matrixSub {rows cols : Nat}
    (left : RatMatrix rows cols)
    (right : ExactFractionMatrix rows cols) :
    exactMatrixValue (matrixSub left right) =
      coreRatMatrixValue left - exactMatrixValue right := by
  apply Matrix.ext
  intro row column
  change
    exactFractionValue
        (ExactFraction.sub
          (ExactFraction.ofRat (left row column))
          (right row column)) =
      left row column - exactFractionValue (right row column)
  calc
    exactFractionValue
        (ExactFraction.sub
          (ExactFraction.ofRat (left row column))
          (right row column)) =
        exactFractionValue (ExactFraction.ofRat (left row column)) -
          exactFractionValue (right row column) :=
      exactFractionValue_sub _ _
    _ = left row column - exactFractionValue (right row column) := by
      rw [exactFractionValue_ofRat]

/-- C006 matrix representation is equality of proof-layer rational matrices. -/
theorem matrixRepresents_iff_exactMatrixValue_eq {rows cols : Nat}
    {raw : ExactFractionMatrix rows cols}
    {canonical : RatMatrix rows cols} :
    MatrixRepresents raw canonical ↔
      exactMatrixValue raw = coreRatMatrixValue canonical := by
  constructor
  · intro h
    apply Matrix.ext
    intro row column
    exact represents_iff_exactFractionValue_eq.mp (h row column)
  · intro h row column
    apply represents_iff_exactFractionValue_eq.mpr
    exact congrFun (congrFun h row) column

/-- Explicit rectangular multiplication commutes with negation of the right
matrix. -/
theorem rationalMatrixMul_neg_right {rows inner cols : Nat}
    (left : RationalMatrix rows inner)
    (right : RationalMatrix inner cols) :
    rationalMatrixMul left (-right) = -rationalMatrixMul left right := by
  apply Matrix.ext
  intro row column
  unfold rationalMatrixMul
  change
    (∑ index, left row index * (-(right index column))) =
      -(∑ index, left row index * right index column)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro index _hIndex
  rw [mul_neg]

/-- C006 and proof-layer interior-solve predicates agree exactly. -/
theorem interiorSolveAgreement {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary) :
    IsInteriorSolve blocks solve ↔ IsMathlibInteriorSolve blocks solve := by
  unfold IsInteriorSolve IsMathlibInteriorSolve
  rw [matrixRepresents_iff_exactMatrixValue_eq]
  rw [exactMatrixValue_matrixMul]
  rfl

/-- The solve convention `X` and harmonic convention `H = -X` agree exactly. -/
theorem harmonicSignAgreement {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary) :
    IsMathlibInteriorSolve blocks solve ↔
      IsHarmonicExtension blocks (-solve) := by
  unfold IsMathlibInteriorSolve IsHarmonicExtension
  rw [rationalMatrixMul_neg_right]
  constructor
  · intro h
    exact congrArg Neg.neg h
  · intro h
    have hNeg := congrArg Neg.neg h
    rw [neg_neg, neg_neg] at hNeg
    exact hNeg

/-- C006 response construction and the proof-layer response formula agree. -/
theorem responseValueAgreement {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (solve : RationalMatrix interior boundary) :
    exactMatrixValue (responseFromSolve blocks solve) =
      mathlibResponseFromSolve blocks solve := by
  unfold responseFromSolve mathlibResponseFromSolve
  rw [exactMatrixValue_matrixSub]
  rw [exactMatrixValue_matrixMul]
  rfl

/-- The exact semantic bridge is inhabited for every ordered C006 block system. -/
theorem exactSemanticBridge {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) :
    ExactSemanticBridge blocks where
  interiorSolveAgreement := interiorSolveAgreement blocks
  harmonicSignAgreement := harmonicSignAgreement blocks
  responseValueAgreement := responseValueAgreement blocks

end CNNAProofs.P001
