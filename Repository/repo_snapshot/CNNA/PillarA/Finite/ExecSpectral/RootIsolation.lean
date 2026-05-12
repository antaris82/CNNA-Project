import CNNA.PillarA.Finite.ExecSpectral.CharpolyCore

set_option autoImplicit false

namespace CNNA.PillarA.Finite.ExecSpectral

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure RationalInterval where
  lower : ℚ
  upper : ℚ
  ordered : lower ≤ upper

namespace RationalInterval

def contains (I : RationalInterval) (q : ℚ) : Prop :=
  I.lower ≤ q ∧ q ≤ I.upper

def center (I : RationalInterval) : ℚ :=
  (I.lower + I.upper) / 2

def radius (I : RationalInterval) : ℚ :=
  (I.upper - I.lower) / 2

theorem lower_le_upper (I : RationalInterval) : I.lower ≤ I.upper :=
  I.ordered

end RationalInterval

structure RootIsolationStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : CharpolyCoreStrong Cell T

abbrev RootIsolationStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  RootIsolationStrong (Cell := Cell) T

namespace RootIsolationStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (R S : RootIsolationStrong Cell T)
    (hsource : R.source = S.source) :
    R = S := by
  cases R with
  | mk sourceR =>
    cases S with
    | mk sourceS =>
      cases hsource
      rfl

def ofCharpoly (C : CharpolyCoreStrong Cell T) :
    RootIsolationStrong Cell T where
  source := C

def cast (h : T = U) (R : RootIsolationStrong Cell T) :
    RootIsolationStrong Cell U := by
  cases h
  exact R

theorem cast_rfl (R : RootIsolationStrong Cell T) :
    cast (Cell := Cell) rfl R = R := by
  rfl

abbrev spectral (R : RootIsolationStrong Cell T) :=
  R.source.spectral

abbrev boxVertex (R : RootIsolationStrong Cell T) :=
  R.spectral.boxVertex

def coordinateCenter (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) : ℚ :=
  (R.spectral.coordinateSpectralValue i).re

theorem coordinateSpectralValue_im_zero (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) :
    (R.spectral.coordinateSpectralValue i).im = 0 := by
  unfold SpectralDecompositionStrong.coordinateSpectralValue
  rw [R.spectral.execMatrix_apply_diag]
  exact ExecComplex.ofRat_im _

theorem coordinateCenter_eq_degreeQ (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) :
    R.coordinateCenter i = R.spectral.degreeQ i := by
  unfold coordinateCenter SpectralDecompositionStrong.coordinateSpectralValue
  rw [R.spectral.execMatrix_apply_diag]
  exact ExecComplex.ofRat_re _

def aroundCoordinate (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) : RationalInterval where
  lower := R.coordinateCenter i - δ
  upper := R.coordinateCenter i + δ
  ordered := by
    simpa [sub_eq_add_neg] using
      add_le_add_left (neg_le_self hδ) (R.coordinateCenter i)

def leftEndpointEval (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) : ExecComplex :=
  R.source.charpolyEval ((R.aroundCoordinate i δ hδ).lower)

def rightEndpointEval (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) : ExecComplex :=
  R.source.charpolyEval ((R.aroundCoordinate i δ hδ).upper)

structure RootIsolationData (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) where
  interval : RationalInterval
  leftEval : ExecComplex
  rightEval : ExecComplex


def coordinateIsolationData (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) :
    RootIsolationData R i δ hδ where
  interval := R.aroundCoordinate i δ hδ
  leftEval := R.leftEndpointEval i δ hδ
  rightEval := R.rightEndpointEval i δ hδ

structure RootIsolationCertificate (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) where
  ordered : (R.aroundCoordinate i δ hδ).lower ≤ (R.aroundCoordinate i δ hδ).upper
  center_eq_degreeQ : R.coordinateCenter i = R.spectral.degreeQ i


def rootIsolationCertificate (R : RootIsolationStrong Cell T)
    (i : R.boxVertex) (δ : ℚ) (hδ : 0 ≤ δ) :
    RootIsolationCertificate R i δ hδ where
  ordered := (R.aroundCoordinate i δ hδ).ordered
  center_eq_degreeQ := R.coordinateCenter_eq_degreeQ i

end RootIsolationStrong

end CNNA.PillarA.Finite.ExecSpectral
