import Init.Data.Fin.Fold
import Init.Data.Int.Lemmas
import Init.Data.Rat.Lemmas
import Init.Tactics

/-!
Paper 1.3.3 / C006 — birth-local Schur/DtN primitive.

C006 defines only the exact fraction-value block-elimination primitive on explicitly
supplied ordered blocks.  Boundary coordinates come first, interior coordinates
second.  The primitive does not choose a cut, build the current network matrix,
prove the M001 cut admissible, or define the inter-birth response R_n.

For blocks

  K = [[K_BB, K_BI], [K_IB, K_II]],

a valid interior solve X satisfies K_II X = K_IB and the response is

  Lambda = K_BB - K_BI X.

Lean keeps supplied entries and solve witnesses on core `Rat` only as a
canonical positive-denominator input encoding.  The finite C006 arithmetic is
self-contained on explicit positive-denominator fractions modulo cross-
multiplication value equality.  C006 does not claim a theorem identifying these
operations with core `Rat.add` / `Rat.mul` / `Rat.sub`; Python agreement is an
external cross-language verification obligation rather than a Lean theorem.

The C006 domain is exact unique solvability of the interior system.  No matrix
transpose, symmetrization, floating threshold, condition number, pseudoinverse,
or regularization is part of this node.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

namespace BirthLocalSchurDtnPrimitive

/-- Core `Rat` matrices used only as canonical positive-denominator input
encodings and solve-witness encodings.  C006 does not invoke core `Rat`
arithmetic. -/
abbrev RatMatrix (rows cols : Nat) := Fin rows → Fin cols → Rat

/-- Constructive exact fraction representation used only for C006 arithmetic.
`denPos` excludes the only invalid rational representation.  Fractions are not
normalized because normalization is irrelevant to exact value semantics. -/
structure ExactFraction where
  num : Int
  den : Nat
  denPos : 0 < den

namespace ExactFraction

/-- Canonical core `Rat` viewed as an exact positive-denominator fraction. -/
def ofRat (q : Rat) : ExactFraction where
  num := q.num
  den := q.den
  denPos := q.den_pos

/-- Exact zero. -/
def zero : ExactFraction where
  num := 0
  den := 1
  denPos := Nat.zero_lt_succ 0

/-- Exact addition without normalization. -/
def add (a b : ExactFraction) : ExactFraction where
  num := a.num * Int.ofNat b.den + b.num * Int.ofNat a.den
  den := a.den * b.den
  denPos := Nat.mul_pos a.denPos b.denPos

/-- Exact multiplication without normalization. -/
def mul (a b : ExactFraction) : ExactFraction where
  num := a.num * b.num
  den := a.den * b.den
  denPos := Nat.mul_pos a.denPos b.denPos

/-- Exact subtraction without normalization. -/
def sub (a b : ExactFraction) : ExactFraction where
  num := a.num * Int.ofNat b.den - b.num * Int.ofNat a.den
  den := a.den * b.den
  denPos := Nat.mul_pos a.denPos b.denPos

/-- Equality of exact fraction values, independent of normalization.
This is the standard positive-denominator fraction equivalence relation. -/
def SameValue (left right : ExactFraction) : Prop :=
  left.num * Int.ofNat right.den = right.num * Int.ofNat left.den

/-- Extensional bridge from a raw exact fraction to canonical core `Rat`.
The equation is cross multiplication, so no `Rat` arithmetic operation occurs. -/
def Represents (raw : ExactFraction) (q : Rat) : Prop :=
  SameValue raw (ofRat q)

/-- Value equality is reflexive. -/
theorem sameValue_refl (value : ExactFraction) : SameValue value value := by
  rfl

/-- Value equality is symmetric. -/
theorem sameValue_symm {left right : ExactFraction}
    (h : SameValue left right) : SameValue right left := by
  exact h.symm

/-- Value equality is transitive because every denominator is nonzero. -/
theorem sameValue_trans {left middle right : ExactFraction}
    (hLeft : SameValue left middle)
    (hRight : SameValue middle right) : SameValue left right := by
  unfold SameValue at hLeft hRight ⊢
  apply Int.eq_of_mul_eq_mul_right
    (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt middle.denPos))
  calc
    (left.num * Int.ofNat right.den) * Int.ofNat middle.den =
        (left.num * Int.ofNat middle.den) * Int.ofNat right.den := by
      ac_rfl
    _ = (middle.num * Int.ofNat left.den) * Int.ofNat right.den :=
      congrArg (fun value => value * Int.ofNat right.den) hLeft
    _ = (middle.num * Int.ofNat right.den) * Int.ofNat left.den := by
      ac_rfl
    _ = (right.num * Int.ofNat middle.den) * Int.ofNat left.den :=
      congrArg (fun value => value * Int.ofNat left.den) hRight
    _ = (right.num * Int.ofNat left.den) * Int.ofNat middle.den := by
      ac_rfl

/-- The exact-fraction value relation is an explicit equivalence relation.
This is the complete internal quotient-value foundation used by C006. -/
theorem sameValue_equivalence :
    (∀ value : ExactFraction, SameValue value value) ∧
    (∀ {left right : ExactFraction}, SameValue left right → SameValue right left) ∧
    (∀ {left middle right : ExactFraction},
      SameValue left middle → SameValue middle right → SameValue left right) :=
  ⟨sameValue_refl, sameValue_symm, sameValue_trans⟩

/-- Core-only two-argument congruence specialized to integer operations.
This avoids relying on `congrArg₂`, which is not present in the project's
Lean 4.31 Init import surface. -/
private theorem congrArgTwoInt
    (operation : Int → Int → Int)
    {left left' right right' : Int}
    (hLeft : left = left')
    (hRight : right = right') :
    operation left right = operation left' right' := by
  cases hLeft
  cases hRight
  rfl

/-- Raw exact addition respects fraction-value equality. -/
theorem add_respects_sameValue {left left' right right' : ExactFraction}
    (hLeft : SameValue left left')
    (hRight : SameValue right right') :
    SameValue (add left right) (add left' right') := by
  unfold SameValue at hLeft hRight ⊢
  change
    (left.num * Int.ofNat right.den + right.num * Int.ofNat left.den) *
        (Int.ofNat left'.den * Int.ofNat right'.den) =
      (left'.num * Int.ofNat right'.den + right'.num * Int.ofNat left'.den) *
        (Int.ofNat left.den * Int.ofNat right.den)
  rw [Int.add_mul, Int.add_mul]
  have hFirst :
      (left.num * Int.ofNat right.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
        (left'.num * Int.ofNat right'.den) *
          (Int.ofNat left.den * Int.ofNat right.den) := by
    calc
      (left.num * Int.ofNat right.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
          (left.num * Int.ofNat left'.den) *
            (Int.ofNat right.den * Int.ofNat right'.den) := by
        ac_rfl
      _ = (left'.num * Int.ofNat left.den) *
            (Int.ofNat right.den * Int.ofNat right'.den) :=
        congrArg
          (fun value => value *
            (Int.ofNat right.den * Int.ofNat right'.den)) hLeft
      _ = (left'.num * Int.ofNat right'.den) *
            (Int.ofNat left.den * Int.ofNat right.den) := by
        ac_rfl
  have hSecond :
      (right.num * Int.ofNat left.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
        (right'.num * Int.ofNat left'.den) *
          (Int.ofNat left.den * Int.ofNat right.den) := by
    calc
      (right.num * Int.ofNat left.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
          (right.num * Int.ofNat right'.den) *
            (Int.ofNat left.den * Int.ofNat left'.den) := by
        ac_rfl
      _ = (right'.num * Int.ofNat right.den) *
            (Int.ofNat left.den * Int.ofNat left'.den) :=
        congrArg
          (fun value => value *
            (Int.ofNat left.den * Int.ofNat left'.den)) hRight
      _ = (right'.num * Int.ofNat left'.den) *
            (Int.ofNat left.den * Int.ofNat right.den) := by
        ac_rfl
  exact congrArgTwoInt (fun first second : Int => first + second) hFirst hSecond

/-- Raw exact multiplication respects fraction-value equality. -/
theorem mul_respects_sameValue {left left' right right' : ExactFraction}
    (hLeft : SameValue left left')
    (hRight : SameValue right right') :
    SameValue (mul left right) (mul left' right') := by
  unfold SameValue at hLeft hRight ⊢
  change
    (left.num * right.num) *
        (Int.ofNat left'.den * Int.ofNat right'.den) =
      (left'.num * right'.num) *
        (Int.ofNat left.den * Int.ofNat right.den)
  calc
    (left.num * right.num) *
        (Int.ofNat left'.den * Int.ofNat right'.den) =
        (left.num * Int.ofNat left'.den) *
          (right.num * Int.ofNat right'.den) := by
      ac_rfl
    _ = (left'.num * Int.ofNat left.den) *
          (right'.num * Int.ofNat right.den) :=
      congrArgTwoInt (fun first second : Int => first * second) hLeft hRight
    _ = (left'.num * right'.num) *
          (Int.ofNat left.den * Int.ofNat right.den) := by
      ac_rfl

/-- Raw exact subtraction respects fraction-value equality. -/
theorem sub_respects_sameValue {left left' right right' : ExactFraction}
    (hLeft : SameValue left left')
    (hRight : SameValue right right') :
    SameValue (sub left right) (sub left' right') := by
  unfold SameValue at hLeft hRight ⊢
  change
    (left.num * Int.ofNat right.den - right.num * Int.ofNat left.den) *
        (Int.ofNat left'.den * Int.ofNat right'.den) =
      (left'.num * Int.ofNat right'.den - right'.num * Int.ofNat left'.den) *
        (Int.ofNat left.den * Int.ofNat right.den)
  rw [Int.sub_mul, Int.sub_mul]
  have hFirst :
      (left.num * Int.ofNat right.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
        (left'.num * Int.ofNat right'.den) *
          (Int.ofNat left.den * Int.ofNat right.den) := by
    calc
      (left.num * Int.ofNat right.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
          (left.num * Int.ofNat left'.den) *
            (Int.ofNat right.den * Int.ofNat right'.den) := by
        ac_rfl
      _ = (left'.num * Int.ofNat left.den) *
            (Int.ofNat right.den * Int.ofNat right'.den) :=
        congrArg
          (fun value => value *
            (Int.ofNat right.den * Int.ofNat right'.den)) hLeft
      _ = (left'.num * Int.ofNat right'.den) *
            (Int.ofNat left.den * Int.ofNat right.den) := by
        ac_rfl
  have hSecond :
      (right.num * Int.ofNat left.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
        (right'.num * Int.ofNat left'.den) *
          (Int.ofNat left.den * Int.ofNat right.den) := by
    calc
      (right.num * Int.ofNat left.den) *
          (Int.ofNat left'.den * Int.ofNat right'.den) =
          (right.num * Int.ofNat right'.den) *
            (Int.ofNat left.den * Int.ofNat left'.den) := by
        ac_rfl
      _ = (right'.num * Int.ofNat right.den) *
            (Int.ofNat left.den * Int.ofNat left'.den) :=
        congrArg
          (fun value => value *
            (Int.ofNat left.den * Int.ofNat left'.den)) hRight
      _ = (right'.num * Int.ofNat left'.den) *
            (Int.ofNat left.den * Int.ofNat right.den) := by
        ac_rfl
  exact congrArgTwoInt (fun first second : Int => first - second) hFirst hSecond

/-- Viewing a canonical `Rat` as a raw exact fraction preserves its value. -/
theorem ofRat_represents (q : Rat) : Represents (ofRat q) q := by
  exact sameValue_refl (ofRat q)

/-- Canonical `Rat` encodings may be replaced by any raw representatives
without changing the internally defined exact-fraction value operations.  This
is an encoding-invariance theorem, not a claim about core `Rat` arithmetic. -/
theorem add_of_representatives {left right : ExactFraction} {p q : Rat}
    (hLeft : Represents left p) (hRight : Represents right q) :
    SameValue (add left right) (add (ofRat p) (ofRat q)) :=
  add_respects_sameValue hLeft hRight

/-- Multiplication is invariant under the choice of input representatives. -/
theorem mul_of_representatives {left right : ExactFraction} {p q : Rat}
    (hLeft : Represents left p) (hRight : Represents right q) :
    SameValue (mul left right) (mul (ofRat p) (ofRat q)) :=
  mul_respects_sameValue hLeft hRight

/-- Subtraction is invariant under the choice of input representatives. -/
theorem sub_of_representatives {left right : ExactFraction} {p q : Rat}
    (hLeft : Represents left p) (hRight : Represents right q) :
    SameValue (sub left right) (sub (ofRat p) (ofRat q)) :=
  sub_respects_sameValue hLeft hRight

/-- Finite left-folded sums respect rational-value equality term by term. -/
theorem foldl_add_respects_sameValue {count : Nat}
    (leftTerms rightTerms : Fin count → ExactFraction)
    (leftInit rightInit : ExactFraction)
    (hTerms : ∀ index, SameValue (leftTerms index) (rightTerms index))
    (hInit : SameValue leftInit rightInit) :
    SameValue
      (Fin.foldl count (fun acc index => add acc (leftTerms index)) leftInit)
      (Fin.foldl count (fun acc index => add acc (rightTerms index)) rightInit) := by
  induction count generalizing leftInit rightInit with
  | zero =>
      rw [Fin.foldl_zero, Fin.foldl_zero]
      exact hInit
  | succ count ih =>
      rw [Fin.foldl_succ, Fin.foldl_succ]
      apply ih
      · intro index
        exact hTerms index.succ
      · exact add_respects_sameValue hInit (hTerms 0)

end ExactFraction

/-- C006 arithmetic result matrices.  Entries are exact but need not be normalized. -/
abbrev ExactFractionMatrix (rows cols : Nat) := Fin rows → Fin cols → ExactFraction

/-- Entrywise equality of rational matrix values, independent of raw
fraction normalization. -/
def MatrixSameValue {rows cols : Nat}
    (left right : ExactFractionMatrix rows cols) : Prop :=
  ∀ i j, ExactFraction.SameValue (left i j) (right i j)

/-- Entrywise bridge from raw fractions to canonical core-`Rat` encodings.
This uses only numerator/denominator cross multiplication. -/
def MatrixRepresents {rows cols : Nat}
    (raw : ExactFractionMatrix rows cols) (canonical : RatMatrix rows cols) : Prop :=
  ∀ i j, ExactFraction.Represents (raw i j) (canonical i j)

/-- Matrix value equality is reflexive. -/
theorem matrixSameValue_refl {rows cols : Nat}
    (matrix : ExactFractionMatrix rows cols) : MatrixSameValue matrix matrix := by
  intro i j
  exact ExactFraction.sameValue_refl (matrix i j)

/-- Matrix value equality is symmetric. -/
theorem matrixSameValue_symm {rows cols : Nat}
    {left right : ExactFractionMatrix rows cols}
    (h : MatrixSameValue left right) : MatrixSameValue right left := by
  intro i j
  exact ExactFraction.sameValue_symm (h i j)

/-- Matrix value equality is transitive. -/
theorem matrixSameValue_trans {rows cols : Nat}
    {left middle right : ExactFractionMatrix rows cols}
    (hLeft : MatrixSameValue left middle)
    (hRight : MatrixSameValue middle right) : MatrixSameValue left right := by
  intro i j
  exact ExactFraction.sameValue_trans (hLeft i j) (hRight i j)

/-- Entrywise value equality is an equivalence relation on raw matrices. -/
theorem matrixSameValue_equivalence {rows cols : Nat} :
    (∀ matrix : ExactFractionMatrix rows cols, MatrixSameValue matrix matrix) ∧
    (∀ {left right : ExactFractionMatrix rows cols},
      MatrixSameValue left right → MatrixSameValue right left) ∧
    (∀ {left middle right : ExactFractionMatrix rows cols},
      MatrixSameValue left middle → MatrixSameValue middle right →
        MatrixSameValue left right) :=
  ⟨matrixSameValue_refl, matrixSameValue_symm, matrixSameValue_trans⟩

/-- Raw row-by-column exact matrix multiplication. -/
def rawMatrixMul {rows inner cols : Nat}
    (left : ExactFractionMatrix rows inner)
    (right : ExactFractionMatrix inner cols) : ExactFractionMatrix rows cols :=
  fun i j =>
    Fin.foldl inner
      (fun acc k => ExactFraction.add acc
        (ExactFraction.mul (left i k) (right k j)))
      ExactFraction.zero

/-- Row-by-column multiplication of canonical input encodings, evaluated
entirely in the internal exact-fraction algebra.  No transpose is implicit and
no core `Rat` arithmetic operation is used. -/
def matrixMul {rows inner cols : Nat}
    (left : RatMatrix rows inner) (right : RatMatrix inner cols) :
    ExactFractionMatrix rows cols :=
  rawMatrixMul
    (fun i k => ExactFraction.ofRat (left i k))
    (fun k j => ExactFraction.ofRat (right k j))

/-- Raw matrix multiplication respects fraction-value equality of both inputs. -/
theorem rawMatrixMul_respects_sameValue {rows inner cols : Nat}
    {left left' : ExactFractionMatrix rows inner}
    {right right' : ExactFractionMatrix inner cols}
    (hLeft : MatrixSameValue left left')
    (hRight : MatrixSameValue right right') :
    MatrixSameValue (rawMatrixMul left right) (rawMatrixMul left' right') := by
  intro i j
  unfold rawMatrixMul
  apply ExactFraction.foldl_add_respects_sameValue
  · intro k
    exact ExactFraction.mul_respects_sameValue (hLeft i k) (hRight k j)
  · exact ExactFraction.sameValue_refl ExactFraction.zero

/-- Raw representatives of canonical input matrices produce the same
internally defined matrix-product value as the canonical encodings. -/
theorem rawMatrixMul_matches_canonicalEncoding {rows inner cols : Nat}
    {leftRaw : ExactFractionMatrix rows inner}
    {rightRaw : ExactFractionMatrix inner cols}
    {left : RatMatrix rows inner} {right : RatMatrix inner cols}
    (hLeft : MatrixRepresents leftRaw left)
    (hRight : MatrixRepresents rightRaw right) :
    MatrixSameValue
      (rawMatrixMul leftRaw rightRaw)
      (matrixMul left right) := by
  unfold MatrixRepresents at hLeft hRight
  unfold matrixMul
  exact rawMatrixMul_respects_sameValue hLeft hRight

/-- Raw entrywise subtraction. -/
def rawMatrixSub {rows cols : Nat}
    (left right : ExactFractionMatrix rows cols) : ExactFractionMatrix rows cols :=
  fun i j => ExactFraction.sub (left i j) (right i j)

/-- Subtract an exact arithmetic result from a canonical input-encoding matrix. -/
def matrixSub {rows cols : Nat}
    (left : RatMatrix rows cols) (right : ExactFractionMatrix rows cols) :
    ExactFractionMatrix rows cols :=
  rawMatrixSub (fun i j => ExactFraction.ofRat (left i j)) right

/-- Raw matrix subtraction respects fraction-value equality. -/
theorem rawMatrixSub_respects_sameValue {rows cols : Nat}
    {left left' right right' : ExactFractionMatrix rows cols}
    (hLeft : MatrixSameValue left left')
    (hRight : MatrixSameValue right right') :
    MatrixSameValue (rawMatrixSub left right) (rawMatrixSub left' right') := by
  intro i j
  exact ExactFraction.sub_respects_sameValue (hLeft i j) (hRight i j)

/-- C006 input block matrix.  Coordinate order inside every block is inherited
from the caller; C006 introduces no permutation. -/
structure OrderedSchurBlocks (boundary interior : Nat) where
  boundaryNonempty : 0 < boundary
  kBB : RatMatrix boundary boundary
  kBI : RatMatrix boundary interior
  kIB : RatMatrix interior boundary
  kII : RatMatrix interior interior

/-- Extensional solve predicate in the internal exact-fraction value algebra.
The computed product is compared by cross multiplication to the canonical
encoding of `K_IB`. -/
def IsInteriorSolve {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (x : RatMatrix interior boundary) : Prop :=
  MatrixRepresents (matrixMul blocks.kII x) blocks.kIB

/-- Exact C006 admissible domain: the encoded interior system has exactly one
canonical `RatMatrix` solve witness under the internal fraction-value equation. -/
def IsInteriorAdmissible {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) : Prop :=
  ∃ x : RatMatrix interior boundary,
    IsInteriorSolve blocks x ∧
      ∀ y : RatMatrix interior boundary, IsInteriorSolve blocks y → y = x

/-- Algebraic response produced from one valid interior solve.  The returned raw
matrix is a deterministic exact representative of K_BB - K_BI X. -/
def responseFromSolve {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (x : RatMatrix interior boundary) : ExactFractionMatrix boundary boundary :=
  matrixSub blocks.kBB (matrixMul blocks.kBI x)

/-- Value-level Schur/DtN response relation.  Lean semantics identifies raw
responses only modulo `MatrixSameValue`.  Python normalization agreement is
verified externally and is not asserted as a core-`Rat` arithmetic theorem. -/
def IsSchurDtnResponse {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (lambda : ExactFractionMatrix boundary boundary) : Prop :=
  ∃ x : RatMatrix interior boundary,
    IsInteriorSolve blocks x ∧
      MatrixSameValue lambda (responseFromSolve blocks x)

/-- Every explicitly supplied valid solve yields a C006 response. -/
theorem response_of_solve {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (x : RatMatrix interior boundary)
    (hSolve : IsInteriorSolve blocks x) :
    IsSchurDtnResponse blocks (responseFromSolve blocks x) := by
  exact ⟨x, hSolve, matrixSameValue_refl (responseFromSolve blocks x)⟩

/-- Exact admissibility supplies at least one Schur/DtN response. -/
theorem response_exists_of_admissible {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hAdmissible : IsInteriorAdmissible blocks) :
    ∃ lambda : ExactFractionMatrix boundary boundary,
      IsSchurDtnResponse blocks lambda := by
  obtain ⟨x, hSolve, _hUnique⟩ := hAdmissible
  exact ⟨responseFromSolve blocks x, response_of_solve blocks x hSolve⟩

/-- The exact C006 response value is independent of both the unique solve
witness and the chosen raw-fraction representative. -/
theorem response_unique_of_admissible {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hAdmissible : IsInteriorAdmissible blocks)
    (left right : ExactFractionMatrix boundary boundary)
    (hLeft : IsSchurDtnResponse blocks left)
    (hRight : IsSchurDtnResponse blocks right) : MatrixSameValue left right := by
  obtain ⟨canonicalSolve, hCanonicalSolve, hUniqueSolve⟩ := hAdmissible
  obtain ⟨leftSolve, hLeftSolve, hLeftValue⟩ := hLeft
  obtain ⟨rightSolve, hRightSolve, hRightValue⟩ := hRight
  have hLeftSolveEq : leftSolve = canonicalSolve :=
    hUniqueSolve leftSolve hLeftSolve
  have hRightSolveEq : rightSolve = canonicalSolve :=
    hUniqueSolve rightSolve hRightSolve
  rw [hLeftSolveEq] at hLeftValue
  rw [hRightSolveEq] at hRightValue
  exact matrixSameValue_trans hLeftValue (matrixSameValue_symm hRightValue)

/-- Replacing a Schur/DtN response by any entrywise value-equivalent raw matrix
preserves the response relation.  This is the explicit Lean↔Python output
representation bridge. -/
theorem response_of_sameValue {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    {left right : ExactFractionMatrix boundary boundary}
    (hResponse : IsSchurDtnResponse blocks right)
    (hValue : MatrixSameValue left right) : IsSchurDtnResponse blocks left := by
  obtain ⟨solve, hSolve, hRightValue⟩ := hResponse
  exact ⟨solve, hSolve, matrixSameValue_trans hValue hRightValue⟩

/-- There is one canonical empty interior solve because `Fin 0` has no rows. -/
def emptyInteriorSolve {boundary : Nat} : RatMatrix 0 boundary :=
  fun i => Fin.elim0 i

/-- The zero-interior system is always solved by the unique empty matrix. -/
theorem zeroInterior_solve {boundary : Nat}
    (blocks : OrderedSchurBlocks boundary 0) :
    IsInteriorSolve blocks emptyInteriorSolve := by
  unfold IsInteriorSolve MatrixRepresents
  intro i
  exact Fin.elim0 i

/-- Therefore the zero-interior boundary case belongs to the exact C006 domain. -/
theorem zeroInterior_admissible {boundary : Nat}
    (blocks : OrderedSchurBlocks boundary 0) :
    IsInteriorAdmissible blocks := by
  refine ⟨emptyInteriorSolve, zeroInterior_solve blocks, ?_⟩
  intro y _hSolve
  funext i
  exact Fin.elim0 i

end BirthLocalSchurDtnPrimitive

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
