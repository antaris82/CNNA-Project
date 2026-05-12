import Mathlib.Analysis.Matrix.Spectrum
import CNNA.PillarA.Finite.SpectralDecompositionCore
import CNNA.PillarA.Foundation.ExecComplexBridge

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

/--
S8c analytic mirror strand.
This module is intentionally separate from the public operative S8 surface.
All spectral data over `ℂ` is confined to this mirror strand as an explicitly marked
local `noncomputable` layer over the mirrored Hermitian matrix.
Later consumers must continue to use the bridge in `Finite/SpectralBridge.lean`
rather than treating this file as a second public production strand.
-/
structure SpectralDecompositionCStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SpectralDecompositionStrong Cell T

abbrev SpectralDecompositionCStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SpectralDecompositionCStrong (Cell := Cell) T

namespace SpectralDecompositionCStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (S R : SpectralDecompositionCStrong Cell T)
    (hsource : S.source = R.source) :
    S = R := by
  cases S with
  | mk sourceS =>
    cases R with
    | mk sourceR =>
      cases hsource
      rfl

def ofSpectral (S : SpectralDecompositionStrong Cell T) :
    SpectralDecompositionCStrong Cell T where
  source := S

def cast (h : T = U) (S : SpectralDecompositionCStrong Cell T) :
    SpectralDecompositionCStrong Cell U := by
  cases h
  exact S

theorem cast_rfl (S : SpectralDecompositionCStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

abbrev boxVertex (S : SpectralDecompositionCStrong Cell T) :=
  S.source.boxVertex

def complexMatrix (S : SpectralDecompositionCStrong Cell T) :
    Matrix S.boxVertex S.boxVertex ℂ :=
  ExecComplexBridge.mapMatrix S.source.execMatrix

theorem complexMatrix_apply (S : SpectralDecompositionCStrong Cell T)
    (i j : S.boxVertex) :
    S.complexMatrix i j = ExecComplexBridge.toComplex (S.source.execMatrix i j) := by
  rfl

theorem complexMatrix_isHermitian (S : SpectralDecompositionCStrong Cell T) :
    IsHermitian S.complexMatrix := by
  exact ExecComplexBridge.map_isHermitian
    (A := S.source.execMatrix) S.source.execMatrix_isHermitian

def complexHermitianMatrix (S : SpectralDecompositionCStrong Cell T) :
    HermitianMatrix (𝕜 := ℂ) (ι := S.boxVertex) where
  matrix := S.complexMatrix
  hermitian := S.complexMatrix_isHermitian

noncomputable def eigenvalues (S : SpectralDecompositionCStrong Cell T) :
    S.boxVertex → ℝ :=
  S.complexMatrix_isHermitian.eigenvalues

noncomputable def eigenvectorBasis (S : SpectralDecompositionCStrong Cell T) :=
  S.complexMatrix_isHermitian.eigenvectorBasis

theorem mulVec_eigenvectorBasis (S : SpectralDecompositionCStrong Cell T)
    (j : S.boxVertex) :
    S.complexMatrix.mulVec ((S.eigenvectorBasis j).ofLp) =
      S.eigenvalues j • ((S.eigenvectorBasis j).ofLp) := by
  unfold eigenvalues eigenvectorBasis
  exact S.complexMatrix_isHermitian.mulVec_eigenvectorBasis j

theorem eigenvalues_mem_spectrum_real (S : SpectralDecompositionCStrong Cell T)
    (i : S.boxVertex) :
    S.eigenvalues i ∈ spectrum ℝ S.complexMatrix := by
  unfold eigenvalues
  exact S.complexMatrix_isHermitian.eigenvalues_mem_spectrum_real i

noncomputable def eigenvectorUnitary (S : SpectralDecompositionCStrong Cell T) :
    ↥(Matrix.unitaryGroup S.boxVertex ℂ) :=
  S.complexMatrix_isHermitian.eigenvectorUnitary

noncomputable def eigenvectorUnitaryMatrix (S : SpectralDecompositionCStrong Cell T) :
    Matrix S.boxVertex S.boxVertex ℂ :=
  ↑(S.eigenvectorUnitary)

theorem eigenvectorUnitary_apply (S : SpectralDecompositionCStrong Cell T)
    (i j : S.boxVertex) :
    S.eigenvectorUnitaryMatrix i j = ((S.eigenvectorBasis j).ofLp) i := by
  unfold eigenvectorUnitaryMatrix eigenvectorUnitary eigenvectorBasis
  exact S.complexMatrix_isHermitian.eigenvectorUnitary_apply i j

theorem eigenvectorUnitary_mulVec_single (S : SpectralDecompositionCStrong Cell T)
    (j : S.boxVertex) :
    S.eigenvectorUnitaryMatrix.mulVec (Pi.single j 1) = (S.eigenvectorBasis j).ofLp := by
  unfold eigenvectorUnitaryMatrix eigenvectorUnitary eigenvectorBasis
  exact S.complexMatrix_isHermitian.eigenvectorUnitary_mulVec j

theorem star_eigenvectorUnitary_mulVec_basis (S : SpectralDecompositionCStrong Cell T)
    (j : S.boxVertex) :
    (star S.eigenvectorUnitaryMatrix).mulVec ((S.eigenvectorBasis j).ofLp) = Pi.single j 1 := by
  unfold eigenvectorUnitaryMatrix eigenvectorUnitary eigenvectorBasis
  exact S.complexMatrix_isHermitian.star_eigenvectorUnitary_mulVec j

noncomputable def eigenvalueDiagonal (S : SpectralDecompositionCStrong Cell T) :
    Matrix S.boxVertex S.boxVertex ℂ :=
  Matrix.diagonal (RCLike.ofReal ∘ S.eigenvalues)

/--
Primary `ℂ`-mirror diagonalization theorem, kept in the exact mathlib target shape.
Consumers that prefer `S.eigenvalueDiagonal` can rewrite by
`simpa [SpectralDecompositionCStrong.eigenvalues, SpectralDecompositionCStrong.eigenvalueDiagonal]`.
-/
theorem unitaryDiagonalization (S : SpectralDecompositionCStrong Cell T) :
    ((Unitary.conjStarAlgAut ℂ (Matrix S.boxVertex S.boxVertex ℂ))
      (star S.complexMatrix_isHermitian.eigenvectorUnitary))
        S.complexMatrix = S.eigenvalueDiagonal := by
  unfold eigenvalueDiagonal eigenvalues
  exact S.complexMatrix_isHermitian.conjStarAlgAut_star_eigenvectorUnitary

/--
Primary `ℂ`-mirror spectral theorem, kept in the exact mathlib target shape.
Consumers that prefer `S.eigenvalueDiagonal` can rewrite by
`simpa [SpectralDecompositionCStrong.eigenvalues, SpectralDecompositionCStrong.eigenvalueDiagonal]`.
-/
theorem spectral_theorem (S : SpectralDecompositionCStrong Cell T) :
    S.complexMatrix =
      ((Unitary.conjStarAlgAut ℂ (Matrix S.boxVertex S.boxVertex ℂ))
        S.complexMatrix_isHermitian.eigenvectorUnitary)
          S.eigenvalueDiagonal := by
  unfold eigenvalueDiagonal eigenvalues
  exact S.complexMatrix_isHermitian.spectral_theorem

theorem charpoly_eq (S : SpectralDecompositionCStrong Cell T) :
    S.complexMatrix.charpoly =
      ∏ i : S.boxVertex, (Polynomial.X - Polynomial.C ((S.eigenvalues i : ℝ) : ℂ)) := by
  unfold eigenvalues
  exact S.complexMatrix_isHermitian.charpoly_eq

theorem roots_charpoly_eq_eigenvalues (S : SpectralDecompositionCStrong Cell T) :
    S.complexMatrix.charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ S.eigenvalues) Finset.univ.val := by
  unfold eigenvalues
  exact S.complexMatrix_isHermitian.roots_charpoly_eq_eigenvalues

theorem splits_charpoly (S : SpectralDecompositionCStrong Cell T) :
    S.complexMatrix.charpoly.Splits := by
  exact S.complexMatrix_isHermitian.splits_charpoly

theorem det_eq_prod_eigenvalues (S : SpectralDecompositionCStrong Cell T) :
    S.complexMatrix.det = ∏ i : S.boxVertex, ((S.eigenvalues i : ℝ) : ℂ) := by
  unfold eigenvalues
  exact S.complexMatrix_isHermitian.det_eq_prod_eigenvalues

theorem trace_eq_sum_eigenvalues (S : SpectralDecompositionCStrong Cell T) :
    S.complexMatrix.trace = ∑ i : S.boxVertex, ((S.eigenvalues i : ℝ) : ℂ) := by
  unfold eigenvalues
  exact S.complexMatrix_isHermitian.trace_eq_sum_eigenvalues

end SpectralDecompositionCStrong

namespace StrengtheningS8c

open CNNA.PillarA.Finite.StrengtheningS8a
open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullSpectralDecompositionC (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    SpectralDecompositionCStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  SpectralDecompositionCStrong.ofSpectral (referenceFullSpectralDecomposition b p wp)

def variationFullSpectralDecompositionC (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    SpectralDecompositionCStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  SpectralDecompositionCStrong.ofSpectral (variationFullSpectralDecomposition β p wp)

end StrengtheningS8c

end CNNA.PillarA.Finite
