import CNNA.PillarA.Finite.ExecSpectral.PolynomialCore

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure CharpolyCoreStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : PolynomialCoreStrong Cell T

abbrev CharpolyCoreStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CharpolyCoreStrong (Cell := Cell) T

namespace CharpolyCoreStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (C D : CharpolyCoreStrong Cell T)
    (hsource : C.source = D.source) :
    C = D := by
  cases C with
  | mk sourceC =>
    cases D with
    | mk sourceD =>
      cases hsource
      rfl

def ofPolynomialCore (P : PolynomialCoreStrong Cell T) :
    CharpolyCoreStrong Cell T where
  source := P

def cast (h : T = U) (C : CharpolyCoreStrong Cell T) :
    CharpolyCoreStrong Cell U := by
  cases h
  exact C

theorem cast_rfl (C : CharpolyCoreStrong Cell T) :
    cast (Cell := Cell) rfl C = C := by
  rfl

abbrev spectral (C : CharpolyCoreStrong Cell T) :=
  C.source.source

abbrev boxVertex (C : CharpolyCoreStrong Cell T) :=
  C.spectral.boxVertex

abbrev evalPolynomial := EvalPolynomial

def charMatrix (C : CharpolyCoreStrong Cell T) :
    Matrix C.boxVertex C.boxVertex EvalPolynomial :=
  fun i j => C.source.charShiftEntry i j

def charEvalMatrix (C : CharpolyCoreStrong Cell T) (q : ℚ) :
    Matrix C.boxVertex C.boxVertex ExecComplex :=
  fun i j => C.charMatrix i j q

def charpolyEval (C : CharpolyCoreStrong Cell T) : EvalPolynomial :=
  fun q => Matrix.det (C.charEvalMatrix q)

def degreeBound (C : CharpolyCoreStrong Cell T) : Nat :=
  Fintype.card C.boxVertex

theorem charEvalMatrix_eq_spectralCharDetMatrix
    (C : CharpolyCoreStrong Cell T) (q : ℚ) :
    C.charEvalMatrix q = C.spectral.spectralCharDetMatrix q := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [charEvalMatrix, charMatrix,
      PolynomialCoreStrong.charShiftEntry_apply_diag,
      SpectralDecompositionStrong.spectralCharDetMatrix]
  · simp [charEvalMatrix, charMatrix,
      PolynomialCoreStrong.charShiftEntry_apply_of_ne,
      SpectralDecompositionStrong.spectralCharDetMatrix, hij]

theorem charpolyEval_apply (C : CharpolyCoreStrong Cell T) (q : ℚ) :
    C.charpolyEval q = Matrix.det (C.spectral.spectralCharDetMatrix q) := by
  unfold charpolyEval
  rw [C.charEvalMatrix_eq_spectralCharDetMatrix q]

theorem charpolyEval_eq_spectralCharDetEval (C : CharpolyCoreStrong Cell T) :
    C.charpolyEval = C.spectral.spectralCharDetEval := by
  funext q
  exact C.charpolyEval_apply q

structure CharpolyShadow (C : CharpolyCoreStrong Cell T) where
  eval : EvalPolynomial
  degreeBound : Nat


def charpolyShadow (C : CharpolyCoreStrong Cell T) : CharpolyShadow C where
  eval := C.charpolyEval
  degreeBound := C.degreeBound

structure CharpolyCoreCertificate (C : CharpolyCoreStrong Cell T) where
  evaluation_agrees : C.charpolyEval = C.spectral.spectralCharDetEval
  degreeBound_eq_card : C.degreeBound = Fintype.card C.boxVertex


def charpolyCoreCertificate (C : CharpolyCoreStrong Cell T) :
    CharpolyCoreCertificate C where
  evaluation_agrees := C.charpolyEval_eq_spectralCharDetEval
  degreeBound_eq_card := rfl

end CharpolyCoreStrong

end CNNA.PillarA.Finite.ExecSpectral
