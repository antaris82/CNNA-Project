import CNNA.PillarA.Finite.SpectralDecompositionCore

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

/--
Executable polynomial shadow over `ExecComplex`.
This stays deliberately on the public computable strand:
a polynomial is represented by its executable evaluation map on `ℚ`.
S8e does not yet claim full coefficient extraction or a closed general
computable eigenbasis package; it only lays out the remaining computable
surface block without reopening the analytic mirror.
-/
abbrev EvalPolynomial := ℚ → ExecComplex

namespace EvalPolynomial

def C (z : ExecComplex) : EvalPolynomial :=
  fun _ => z

def X : EvalPolynomial :=
  fun q => ExecComplex.ofRat q

def eval (p : EvalPolynomial) (q : ℚ) : ExecComplex :=
  p q

def add (p r : EvalPolynomial) : EvalPolynomial :=
  fun q => p q + r q

def neg (p : EvalPolynomial) : EvalPolynomial :=
  fun q => -p q

def sub (p r : EvalPolynomial) : EvalPolynomial :=
  fun q => p q - r q

def mul (p r : EvalPolynomial) : EvalPolynomial :=
  fun q => p q * r q

def pow (p : EvalPolynomial) : Nat → EvalPolynomial
  | 0 => C 1
  | n + 1 => mul p (pow p n)

theorem C_apply (z : ExecComplex) (q : ℚ) :
    C z q = z := by
  rfl

theorem X_apply (q : ℚ) :
    X q = ExecComplex.ofRat q := by
  rfl

theorem eval_def (p : EvalPolynomial) (q : ℚ) :
    eval p q = p q := by
  rfl

theorem add_apply (p r : EvalPolynomial) (q : ℚ) :
    add p r q = p q + r q := by
  rfl

theorem neg_apply (p : EvalPolynomial) (q : ℚ) :
    neg p q = -p q := by
  rfl

theorem sub_apply (p r : EvalPolynomial) (q : ℚ) :
    sub p r q = p q - r q := by
  rfl

theorem mul_apply (p r : EvalPolynomial) (q : ℚ) :
    mul p r q = p q * r q := by
  rfl

theorem pow_zero_apply (p : EvalPolynomial) (q : ℚ) :
    pow p 0 q = 1 := by
  rfl

theorem pow_succ_apply (p : EvalPolynomial) (n : Nat) (q : ℚ) :
    pow p (n + 1) q = p q * pow p n q := by
  rfl

end EvalPolynomial

structure PolynomialCoreStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SpectralDecompositionStrong Cell T

abbrev PolynomialCoreStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  PolynomialCoreStrong (Cell := Cell) T

namespace PolynomialCoreStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (P Q : PolynomialCoreStrong Cell T)
    (hsource : P.source = Q.source) :
    P = Q := by
  cases P with
  | mk sourceP =>
    cases Q with
    | mk sourceQ =>
      cases hsource
      rfl

def ofSpectral (S : SpectralDecompositionStrong Cell T) :
    PolynomialCoreStrong Cell T where
  source := S

def cast (h : T = U) (P : PolynomialCoreStrong Cell T) :
    PolynomialCoreStrong Cell U := by
  cases h
  exact P

theorem cast_rfl (P : PolynomialCoreStrong Cell T) :
    cast (Cell := Cell) rfl P = P := by
  rfl

abbrev boxVertex (P : PolynomialCoreStrong Cell T) :=
  P.source.boxVertex

abbrev polynomial := EvalPolynomial

def constant (_P : PolynomialCoreStrong Cell T) (z : ExecComplex) : EvalPolynomial :=
  EvalPolynomial.C z

def indeterminate (_P : PolynomialCoreStrong Cell T) : EvalPolynomial :=
  EvalPolynomial.X

def matrixEntryConstant (P : PolynomialCoreStrong Cell T)
    (i j : P.boxVertex) : EvalPolynomial :=
  P.constant (P.source.execMatrix i j)

def diagonalValuePolynomial (P : PolynomialCoreStrong Cell T)
    (i : P.boxVertex) : EvalPolynomial :=
  P.constant (P.source.coordinateSpectralValue i)

def charShiftEntry (P : PolynomialCoreStrong Cell T)
    (i j : P.boxVertex) : EvalPolynomial :=
  if i = j then
    EvalPolynomial.sub (P.indeterminate) (P.matrixEntryConstant i j)
  else
    EvalPolynomial.neg (P.matrixEntryConstant i j)

theorem constant_apply (P : PolynomialCoreStrong Cell T)
    (z : ExecComplex) (q : ℚ) :
    P.constant z q = z := by
  rfl

theorem indeterminate_apply (P : PolynomialCoreStrong Cell T) (q : ℚ) :
    P.indeterminate q = ExecComplex.ofRat q := by
  rfl

theorem matrixEntryConstant_apply (P : PolynomialCoreStrong Cell T)
    (i j : P.boxVertex) (q : ℚ) :
    P.matrixEntryConstant i j q = P.source.execMatrix i j := by
  rfl

theorem diagonalValuePolynomial_apply (P : PolynomialCoreStrong Cell T)
    (i : P.boxVertex) (q : ℚ) :
    P.diagonalValuePolynomial i q = P.source.coordinateSpectralValue i := by
  rfl

theorem charShiftEntry_apply_diag (P : PolynomialCoreStrong Cell T)
    (i : P.boxVertex) (q : ℚ) :
    P.charShiftEntry i i q =
      ExecComplex.ofRat q - P.source.execMatrix i i := by
  simp [charShiftEntry, EvalPolynomial.sub_apply,
    indeterminate_apply, matrixEntryConstant_apply]

theorem charShiftEntry_apply_of_ne (P : PolynomialCoreStrong Cell T)
    {i j : P.boxVertex} (hij : i ≠ j) (q : ℚ) :
    P.charShiftEntry i j q = -P.source.execMatrix i j := by
  simp [charShiftEntry, hij, EvalPolynomial.neg_apply, matrixEntryConstant_apply]

structure PolynomialCoreCertificate (P : PolynomialCoreStrong Cell T) where
  indeterminate_shadow : ∀ q : ℚ, P.indeterminate q = ExecComplex.ofRat q
  charShift_diag : ∀ i : P.boxVertex, ∀ q : ℚ,
    P.charShiftEntry i i q = ExecComplex.ofRat q - P.source.execMatrix i i
  charShift_offDiag : ∀ {i j : P.boxVertex}, i ≠ j → ∀ q : ℚ,
    P.charShiftEntry i j q = -P.source.execMatrix i j

def polynomialCoreCertificate (P : PolynomialCoreStrong Cell T) :
    PolynomialCoreCertificate P where
  indeterminate_shadow := P.indeterminate_apply
  charShift_diag := P.charShiftEntry_apply_diag
  charShift_offDiag := by
    intro i j hij q
    exact P.charShiftEntry_apply_of_ne hij q

end PolynomialCoreStrong

end CNNA.PillarA.Finite.ExecSpectral
